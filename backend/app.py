# ==========================
# IMPORTACIONES Y CONFIGURACIÓN
# ==========================
from flask import Flask, request, redirect, session, jsonify
import sqlglot
import time
import json
import os
import re
import csv
from io import StringIO
import datetime
import shutil
from flask_cors import CORS
import unicodedata
from google_auth_oauthlib.flow import Flow
from googleapiclient.discovery import build
from googleapiclient.http import MediaFileUpload
import pathlib
from google.oauth2 import id_token
from google.auth.transport import requests as grequests
# ==========================
# CONSTANTES Y APP FLASK
# ==========================
app = Flask(__name__)
CORS(app, supports_credentials=True)
DATA_DIR = "data"
app.secret_key = "una_clave_secreta_segura"

os.environ["OAUTHLIB_INSECURE_TRANSPORT"] = "1"

CLIENT_SECRETS_FILE = "credentials.json"
SCOPES = ["https://www.googleapis.com/auth/drive.file"]
# ==========================
# FUNCIONES UTILITARIAS
# ==========================
def save_table(db, table, data):
    os.makedirs(os.path.join(DATA_DIR, db), exist_ok=True)
    with open(os.path.join(DATA_DIR, db, f"{table}.json"), "w") as f:
        json.dump(data, f)

def is_valid_name(name):
    return re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*$', name) is not None

def load_table(db, table):
    try:
        with open(os.path.join(DATA_DIR, db, f"{table}.json"), "r") as f:
            return json.load(f)
    except FileNotFoundError:
        return []

def backup_table(db, table, data):
    backup_dir = os.path.join(DATA_DIR, db, "backups")
    os.makedirs(backup_dir, exist_ok=True)
    timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_file = os.path.join(backup_dir, f"{table}_{timestamp}.json")
    with open(backup_file, "w") as f:
        json.dump(data, f)

def parse_db_table(full_name):
    # Elimina alias si existe (por ejemplo: "tienda.clientes AS c" -> "tienda.clientes")
    full_name = full_name.split(" AS ")[0].split(" as ")[0].strip()
    parts = full_name.split('.')
    if len(parts) == 2:
        return parts[0], parts[1]
    return None, parts[0]

def normalizar(texto):
    if texto is None:
        return ""
    # Quita acentos, pasa a minúsculas y elimina espacios extra
    texto = str(texto).strip().lower()
    texto = ''.join(c for c in unicodedata.normalize('NFD', texto)
                    if unicodedata.category(c) != 'Mn')
    return texto

def join_tables(left_rows, right_rows, left_key, right_key):
    result = []
    for l in left_rows:
        for r in right_rows:
            if normalizar(l.get(left_key)) == normalizar(r.get(right_key)):
                combined = {**l, **r}
                result.append(combined)
    return result

def group_by_agg(rows, group_col, agg_col, agg_func):
    groups = {}
    for row in rows:
        key = row[group_col]
        groups.setdefault(key, []).append(row)
    result = []
    for key, group_rows in groups.items():
        if agg_func == "SUM":
            agg_value = sum(float(r[agg_col]) for r in group_rows)
        elif agg_func == "COUNT":
            agg_value = len(group_rows)
        else:
            agg_value = None
        result.append({group_col: key, f"{agg_func.lower()}_{agg_col}": agg_value})
    return result


# ==========================
# CACHE DE RESULTADOS DE CONSULTAS
# ==========================
query_cache = {}

# ==========================
# CICLO DE VIDA DE UNA CONSULTA SQL
# ==========================

def parser(query):
    """Etapa 1: Parser - Analiza y valida la sintaxis SQL."""
    parsed = sqlglot.parse(query)
    print(parsed[0].dump())
    if not parsed or len(parsed) == 0:
        raise ValueError("Consulta SQL vacía o inválida")
    return parsed[0]

def algebrizer(stmt):
    """
    Etapa 2: Algebrizer mejorado.
    Extrae tipo de sentencia, tablas, columnas, joins y group by del AST de sqlglot.
    """
    info = {
        "type": stmt.key.upper(),
        "tables": [],
        "columns": [],
        "joins": [],
        "group_by": [],
        "aggregates": []
    }
    # Tablas principales
    if hasattr(stmt, "args") and "from" in stmt.args and stmt.args["from"]:
        main_table = stmt.args["from"].args["this"]
        info["tables"].append(str(main_table))
    # Columnas seleccionadas y agregaciones
    if hasattr(stmt, "args") and "expressions" in stmt.args and stmt.args["expressions"]:
        for expr in stmt.args["expressions"]:
            if expr.key.upper() in ("SUM", "COUNT"):
                info["aggregates"].append({
                    "func": expr.key.upper(),
                    "col": str(expr.args["this"]),
                    "alias": getattr(expr, "alias", None)
                })
            else:
                info["columns"].append(getattr(expr, "alias", None) or getattr(expr, "name", None) or str(expr))
    # Joins
    if hasattr(stmt, "args") and "joins" in stmt.args and stmt.args["joins"]:
        for join in stmt.args["joins"]:
            join_table = join.args["this"]
            on_expr = join.args["on"]
            info["joins"].append({
                "table": str(join_table),
                "on_left": str(on_expr.args["this"]),
                "on_right": str(on_expr.args["expression"])
            })
    # Group by
    if hasattr(stmt, "args") and "group" in stmt.args and stmt.args["group"]:
        for gexpr in stmt.args["group"].expressions:
            info["group_by"].append(str(gexpr))
    return info

def optimizer(stmt_type, query):
    """Etapa 3: Optimizer/Planner - Usa caché para SELECT, plan simple para otros."""
    if stmt_type == "SELECT" and query in query_cache:
        return {"plan": "cache", "cached_result": query_cache[query]}
    return {"plan": "execute", "query": query}

def executor(plan, stmt_type, query, data, stmt_info):
    """Etapa 4: Executor - Ejecuta el plan (toda tu lógica real aquí)."""
    # SELECT con caché
    if plan.get("plan") == "cache":
        return {"source": "cache", **plan["cached_result"]}

    # --- Lógica para SELECT usando stmt_info ---
    if stmt_type == "SELECT":
        # JOIN simple
        if stmt_info["joins"]:
            main_table = stmt_info["tables"][0]
            join = stmt_info["joins"][0]
            join_table = join["table"]
            left_col = join["on_left"].split(".")[-1]
            right_col = join["on_right"].split(".")[-1]
            db1, t1 = parse_db_table(main_table)
            db2, t2 = parse_db_table(join_table)
            rows1 = load_table(db1, t1)["rows"]
            rows2 = load_table(db2, t2)["rows"]
            joined = join_tables(rows1, rows2, left_col, right_col)

            # Si hay GROUP BY, agrupa sobre el resultado del JOIN
            if stmt_info["group_by"]:
                group_cols = [col for col in stmt_info["group_by"]]
                result = []
                groups = {}
                for row in joined:
                    key = tuple(row[col.split(".")[-1]] for col in group_cols)
                    groups.setdefault(key, []).append(row)
                for key, group_rows in groups.items():
                    result_row = {col.split(".")[-1]: val for col, val in zip(group_cols, key)}
                    for agg in stmt_info["aggregates"]:
                        agg_func = agg["func"]
                        agg_col = agg["col"].split(".")[-1]
                        alias = agg["alias"] or f"{agg_func.lower()}_{agg_col}"
                        if agg_func == "SUM":
                            agg_value = sum(float(r.get(agg_col, 0)) for r in group_rows)
                        elif agg_func == "COUNT":
                            agg_value = len(group_rows)
                        else:
                            agg_value = None
                        result_row[alias] = agg_value
                    result.append(result_row)
                    # Inferir columnas a partir de las keys del primer row
                columns = list(result[0].keys()) if result else []

                return {
                    "source": "executed",
                    "columns": columns,
                    "rows": result
                }


            else:
                # Si no hay GROUP BY, solo selecciona columnas del JOIN
                result = []
                for row in joined:
                    result_row = {}
                    for col in stmt_info["columns"]:
                        if "." in col:
                            _, real_col = col.split(".", 1)
                        else:
                            real_col = col
                        result_row[col] = row.get(real_col)
                    for agg in stmt_info["aggregates"]:
                        alias = agg["alias"] or f"{agg['func'].lower()}_{agg['col']}"
                        if agg["func"] == "SUM":
                            result_row[alias] = float(row.get(agg["col"], 0))
                        elif agg["func"] == "COUNT":
                            result_row[alias] = 1
                    result.append(result_row)

                # Aquí infieres las columnas
                columns = list(result[0].keys()) if result else []

                # Y las devuelves
                return {
                    "source": "executed",
                    "columns": columns,
                    "rows": result
                }


        # SELECT simple (sin JOIN ni GROUP BY)
        if stmt_info["tables"]:
            db, table = parse_db_table(stmt_info["tables"][0])
            table_data = load_table(db, table)
            if not table_data:
                raise ValueError(f'Tabla {table} no existe en base {db}')
            if stmt_info["columns"] == ["*"]:
                # Devuelve todas las columnas
                result = [row for row in table_data["rows"]]
                column_names = [col['name'] for col in table_data["columns"]]
            else:
                result = [{col: row.get(col) for col in stmt_info["columns"]} for row in table_data["rows"]]
                column_names = stmt_info["columns"]
            query_cache[query] = {"columns": column_names, "rows": result}
            return {"source": "executed", "columns": column_names, "rows": result}
    
    # CREATE DATABASE
    if query.lower().startswith("create database"):
        match = re.match(r"create database (\w+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para CREATE DATABASE')
        db_name = match.group(1)
        if not is_valid_name(db_name):
            raise ValueError('Nombre de base de datos inválido')
        db_path = os.path.join(DATA_DIR, db_name)
        if os.path.exists(db_path):
            raise ValueError(f'La base de datos {db_name} ya existe')
        os.makedirs(db_path, exist_ok=True)
        query_cache.clear()
        return {'message': f'Base de datos {db_name} creada'}
    
    # SHOW DATABASES
    if query.lower().startswith("show databases"):
        dbs = [d for d in os.listdir(DATA_DIR) if os.path.isdir(os.path.join(DATA_DIR, d))]
        return {'databases': dbs}
    
    # RENAME DATABASE
    if query.lower().startswith("rename database"):
        match = re.match(r"rename database (\w+) to (\w+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para RENAME DATABASE. Usa RENAME DATABASE db_antigua TO db_nueva')
        old_db, new_db = match.groups()
        if not is_valid_name(old_db) or not is_valid_name(new_db):
            raise ValueError('Nombre de base de datos inválido')
        old_path = os.path.join(DATA_DIR, old_db)
        new_path = os.path.join(DATA_DIR, new_db)
        if not os.path.exists(old_path):
            raise ValueError(f'La base de datos {old_db} no existe')
        if os.path.exists(new_path):
            raise ValueError(f'La base de datos {new_db} ya existe')
        os.rename(old_path, new_path)
        query_cache.clear()
        return {'message': f'Base de datos {old_db} renombrada a {new_db}'}
    
    # DROP DATABASE
    if query.lower().startswith("drop database"):
        match = re.match(r"drop database (\w+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para DROP DATABASE')
        db_name = match.group(1)
        if not is_valid_name(db_name):
            raise ValueError('Nombre de base de datos inválido')
        db_path = os.path.join(DATA_DIR, db_name)
        if not os.path.exists(db_path):
            raise ValueError(f'La base de datos {db_name} no existe')
        shutil.rmtree(db_path)
        query_cache.clear()
        return {'message': f'Base de datos {db_name} eliminada'}

    # CREATE TABLE
    if query.lower().startswith("create table"):
        match = re.match(r"create table (\w+\.\w+|\w+)\s*\(([\s\S]+)\)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para CREATE TABLE')
        full_table, columns = match.groups()
        db, table = parse_db_table(full_table)
        if not db or not is_valid_name(db) or not is_valid_name(table):
            raise ValueError('Nombre de base de datos o tabla inválido')
        # Tipos permitidos
        allowed_types = [
            'INT', 'BIGINT', 'DECIMAL', 'FLOAT', 'NUMERIC',
            'VARCHAR', 'CHAR', 'TEXT', 'NVARCHAR',
            'DATE', 'DATETIME', 'TIMESTAMP',
            'BIT',
            'BLOB', 'VARBINARY',
            'JSON', 'XML', 'GEOMETRY'
        ]
        columns_list = []
        for col_def in columns.replace('\n', '').split(','):
            col_def = col_def.strip().strip(',')
            if not col_def:
                continue
            parts = col_def.split()
            if len(parts) < 2:
                raise ValueError('Cada columna debe tener nombre y tipo, por ejemplo: id INT')
            col_name = parts[0]
            col_type = ' '.join(parts[1:]).upper()
            # Permitir tipos con parámetros, como VARCHAR(50)
            base_type = re.match(r'^\w+', col_type)
            if not is_valid_name(col_name):
                raise ValueError(f'Nombre de columna inválido: {col_name}')
            if not base_type or base_type.group(0) not in allowed_types:
                raise ValueError(f'Tipo de columna no soportado: {col_type}')
            columns_list.append({"name": col_name, "type": col_type})
        if len(set(col['name'] for col in columns_list)) != len(columns_list):
            raise ValueError('No puede haber columnas repetidas')
        table_path = os.path.join(DATA_DIR, db, f"{table}.json")
        if os.path.exists(table_path):
            raise ValueError(f'La tabla {table} ya existe en base {db}')
        save_table(db, table, {"columns": columns_list, "rows": []})
        query_cache.clear()
        return {'message': f'Tabla {table} creada en base {db} con columnas {columns_list}'}


    # DROP TABLE
    if query.lower().startswith("drop table"):
        match = re.match(r"drop table (\w+\.\w+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para DROP TABLE. Usa DROP TABLE db.tabla')
        full_table = match.group(1)
        db, table = parse_db_table(full_table)
        if not db or not is_valid_name(db) or not is_valid_name(table):
            raise ValueError('Nombre de base de datos o tabla inválido')
        table_path = os.path.join(DATA_DIR, db, f"{table}.json")
        if not os.path.exists(table_path):
            raise ValueError(f'La tabla {table} no existe en base {db}')
        os.remove(table_path)
        query_cache.clear()
        return {'message': f'Tabla {table} eliminada de la base {db}'}

    # RENAME TABLE
    if query.lower().startswith("rename table"):
        match = re.match(r"rename table (\w+\.\w+) to (\w+\.\w+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para RENAME TABLE. Usa RENAME TABLE db.tabla TO db.nuevonombre')
        full_table, full_new = match.groups()
        db, table = parse_db_table(full_table)
        db_new, table_new = parse_db_table(full_new)
        if not db or not db_new or db != db_new or not is_valid_name(table_new):
            raise ValueError('Ambas tablas deben estar en la misma base de datos y tener nombres válidos')
        old_path = os.path.join(DATA_DIR, db, f"{table}.json")
        new_path = os.path.join(DATA_DIR, db, f"{table_new}.json")
        if not os.path.exists(old_path):
            raise ValueError(f'La tabla {table} no existe en base {db}')
        if os.path.exists(new_path):
            raise ValueError(f'La tabla {table_new} ya existe en base {db}')
        os.rename(old_path, new_path)
        query_cache.clear()
        return {'message': f'Tabla {table} renombrada a {table_new} en base {db}'}

    # INSERT
    if query.lower().startswith("insert into"):
        match = re.match(r"insert into (\w+\.\w+|\w+)\s*\(([\s\S]+?)\)\s*values\s*\(([\s\S]+?)\)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para INSERT')
        full_table, columns, values = match.groups()
        db, table = parse_db_table(full_table)
        if not db or not is_valid_name(db) or not is_valid_name(table):
            raise ValueError('Nombre de base de datos o tabla inválido')
        columns = [c.strip() for c in columns.split(',')]
        values = [v.strip().strip("'") for v in values.split(',')]
        table_data = load_table(db, table)
        if not table_data:
            raise ValueError(f'Tabla {table} no existe en base {db}')
        # Validar columnas
        table_columns = [col['name'] for col in table_data["columns"]]
        print(f"columns: {columns}")
        print(f"table_columns: {table_columns}")
        if set(columns) != set(table_columns):
            raise ValueError('Debes insertar todas las columnas de la tabla y en el mismo orden')
        # Validar tipos
        for i, col in enumerate(table_data["columns"]):
            col_name = col["name"]
            col_type = col["type"].upper()
            val = values[i]
            base_type = re.match(r'^([A-Z]+)', col_type).group(1)
            if base_type in ['INT', 'BIGINT']:
                if not re.match(r'^-?\d+$', val):
                    raise ValueError(f'El valor para {col_name} debe ser un entero')
            elif base_type in ['DECIMAL', 'FLOAT', 'NUMERIC']:
                if not re.match(r'^-?\d+(\.\d+)?$', val):
                    raise ValueError(f'El valor para {col_name} debe ser numérico')
            elif base_type in ['BIT']:
                if val not in ['0', '1', 'True', 'False', 'true', 'false']:
                    raise ValueError(f'El valor para {col_name} debe ser booleano (0/1 o True/False)')
            elif base_type in ['DATE', 'DATETIME', 'TIMESTAMP']:
                try:
                    datetime.datetime.fromisoformat(val)
                except Exception:
                    raise ValueError(f'El valor para {col_name} debe ser una fecha válida (YYYY-MM-DD o similar)')
            elif base_type in ['VARCHAR', 'CHAR', 'NVARCHAR']:
                # Extraer longitud si existe, por ejemplo VARCHAR(20)
                length_match = re.search(r'\((\d+)\)', col_type)
                if length_match:
                    max_len = int(length_match.group(1))
                    if len(val) > max_len:
                        raise ValueError(f'El valor para {col_name} excede la longitud máxima de {max_len} caracteres')
                if base_type == 'CHAR' and length_match:
                    if len(val) != max_len:
                        raise ValueError(f'El valor para {col_name} debe tener exactamente {max_len} caracteres')
        row = dict(zip(columns, values))
        table_data["rows"].append(row)
        save_table(db, table, table_data)
        query_cache.clear()
        return {'message': f'Dato insertado en {table} de {db}', 'row': row}


    # UPDATE
    if query.lower().startswith("update"):
        match = re.match(r"update (\w+\.\w+|\w+) set (.+) where (.+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para UPDATE')
        full_table, set_part, where_part = match.groups()
        db, table = parse_db_table(full_table)
        if not db or not is_valid_name(db) or not is_valid_name(table):
            raise ValueError('Nombre de base de datos o tabla inválido')
        table_data = load_table(db, table)
        if not table_data:
            raise ValueError(f'Tabla {table} no existe en base {db}')
        backup_table(db, table, table_data)
        set_col, set_val = [x.strip() for x in set_part.split('=')]
        where_col, where_val = [x.strip() for x in where_part.split('=')]
        set_val = set_val.strip("'")
        where_val = where_val.strip("'")
        column_names = [col["name"] for col in table_data["columns"]]
        if set_col not in column_names:
            raise ValueError(f'Columna {set_col} no existe en la tabla {table}')
        if where_col not in column_names:
            raise ValueError(f'Columna {where_col} no existe en la tabla {table}')
        updated = 0
        for row in table_data["rows"]:
            if str(row.get(where_col)) == where_val:
                row[set_col] = set_val
                updated += 1
        save_table(db, table, table_data)
        query_cache.clear()
        return {'message': f'{updated} filas actualizadas en {table} de {db}'}

    # DELETE
    if query.lower().startswith("delete from"):
        match = re.match(r"delete from (\w+\.\w+|\w+) where (\w+)\s*(=|<|>|<=|>=|!=)\s*(.+)", query, re.IGNORECASE)
        if not match:
            raise ValueError('Sintaxis inválida para DELETE')
        full_table, where_col, operator, where_val = match.groups()
        db, table = parse_db_table(full_table)
        if not db or not is_valid_name(db) or not is_valid_name(table):
            raise ValueError('Nombre de base de datos o tabla inválido')
        table_data = load_table(db, table)
        if not table_data:
            raise ValueError(f'Tabla {table} no existe en base {db}')
        backup_table(db, table, table_data)
        where_val = where_val.strip("'")
        column_names = [col["name"] for col in table_data["columns"]]
        if where_col not in column_names:
            raise ValueError(f'Columna {where_col} no existe en la tabla {table}')

        def compare(val1, op, val2):
            try:
                val1 = float(val1)
                val2 = float(val2)
            except:
                pass  # si no son numéricos, se comparan como strings
            if op == "=":
                return val1 == val2
            elif op == ">":
                return val1 > val2
            elif op == "<":
                return val1 < val2
            elif op == ">=":
                return val1 >= val2
            elif op == "<=":
                return val1 <= val2
            elif op == "!=":
                return val1 != val2
            else:
                raise ValueError("Operador desconocido")

        before = len(table_data["rows"])
        table_data["rows"] = [
            row for row in table_data["rows"]
            if not compare(row.get(where_col), operator, where_val)
        ]
        deleted = before - len(table_data["rows"])
        save_table(db, table, table_data)
        query_cache.clear()
        return {'message': f'{deleted} filas eliminadas de {table} en {db}'}


    raise ValueError('Solo se soportan CREATE TABLE, INSERT, SELECT, UPDATE y DELETE básicos con db.tabla')

# ==========================
# ENDPOINT PRINCIPAL: EJECUCIÓN DE SQL (modularizado)
# ==========================

@app.route('/execute', methods=['POST'])
def execute_sql():
    """
    Recibe una consulta SQL y ejecuta todas las etapas del ciclo de vida:
    Parser -> Algebrizer -> Optimizer/Planner -> Executor (con caché)
    """
    data = request.json
    query = data.get('query', '').strip()
    try:
        tiempo_inicio = time.time() # TIEMPO INICIO
        # 1. Parser
        stmt = parser(query)
        # 2. Algebrizer
        stmt_info = algebrizer(stmt)
        stmt_type = stmt_info["type"]
        if stmt_type not in ['SELECT', 'INSERT', 'UPDATE', 'DELETE', 'CREATE', 'DROP', 'COMMAND']:
            return jsonify({'error': f'Tipo de consulta no soportado: {stmt_type}'}), 400
        # 3. Optimizer/Planner (incluye caché)
        plan = optimizer(stmt_type, query)
        # 4. Executor
        result = executor(plan, stmt_type, query, data, stmt_info)
        tiempo_ejecucion = time.time()-tiempo_inicio
        print("Data:", result)
        result['execution_time'] = tiempo_ejecucion # TIEMPO DE EJECUCIÓN

        # FILAS AFECTADAS
        if "rows" in result and isinstance(result["rows"], list):
            result["rows_affected"] = len(result["rows"])
        elif "message" in result and "filas" in result["message"]:
            import re
            match = re.search(r'(\d+)\s+filas?', result["message"])
            if match:
                result["rows_affected"] = int(match.group(1))
        filas_afectadas = result.get("rows_affected", 0)
        if filas_afectadas is None:
            filas_afectadas = 0

        result["rows_affected"] = filas_afectadas = result.get("rows_affected", 0)
        print(f"Consulta ejecutada en {tiempo_ejecucion:.4f} segundos") # IMPRIMIR TIEMPO DE EJECUCIÓN
        print(f"{filas_afectadas}") # IMPRIMIR FILAS AFECTADAS

        return jsonify(result)
    except Exception as e:
        return jsonify({'error': str(e)}), 400
# ==========================
# ENDPOINTS DE ADMINISTRACIÓN
# ==========================

@app.route("/login", methods=["POST"])
def login():
    data = request.get_json()
    username = data.get('username', '').strip().lower()
    password = data.get('password', '').strip()
    if not username or not password:
        return jsonify({'success': False, 'error': 'Usuario y contraseña requeridos'}), 400
    if os.path.exists(USERS_FILE):
        with open(USERS_FILE, 'r', encoding='utf-8') as f:
            try:
                users = json.load(f)
            except Exception:
                users = {}
    else:
        users = {}
    if username not in users or users[username] != password:
        return jsonify({'success': False, 'error': 'Usuario o contraseña incorrectos'}), 401
    return jsonify({'success': True}), 200

@app.route("/oauth2callback")
def oauth2callback():
    flow = Flow.from_client_secrets_file(
        CLIENT_SECRETS_FILE,
        scopes=SCOPES,
        redirect_uri="http://localhost:5000/oauth2callback"
    )
    flow.fetch_token(authorization_response=request.url)

    credentials = flow.credentials
    session["credentials"] = {
        "token": credentials.token,
        "refresh_token": credentials.refresh_token,
        "token_uri": credentials.token_uri,
        "client_id": credentials.client_id,
        "client_secret": credentials.client_secret,
        "scopes": credentials.scopes,
    }
    return redirect("/upload_to_drive")

@app.route("/upload_to_drive", methods=["GET", "POST"])
def upload_to_drive():
    if "credentials" not in session:
        return redirect("/login")

    if request.method == "GET":
        return '''
        <form method="POST" enctype="multipart/form-data">
            <input type="file" name="file"><br>
            <input type="submit" value="Subir a Drive">
        </form>
        '''

    credentials = session["credentials"]
    file = request.files["file"]
    filepath = f"temp_{file.filename}"
    file.save(filepath)

    from google.oauth2.credentials import Credentials
    creds = Credentials(**credentials)

    service = build("drive", "v3", credentials=creds)

    file_metadata = {"name": file.filename}
    media = MediaFileUpload(filepath, resumable=True)
    uploaded_file = service.files().create(body=file_metadata, media_body=media, fields="id").execute()

    os.remove(filepath)
    return jsonify({"message": "Archivo subido a Drive", "file_id": uploaded_file.get("id")})

@app.route("/google-login", methods=["POST"])
def google_login():
    token = request.json.get("credential")
    try:
        idinfo = id_token.verify_oauth2_token(token, grequests.Request(), "154709914760-lj5hq85pps2fumarjoofeed8kptdm4gp.apps.googleusercontent.com")

        # Aquí puedes crear el usuario en tu base de datos si no existe
        user_email = idinfo["email"]
        user_name = idinfo.get("name", "")

        return jsonify({
            "success": True,
            "user": {
                "email": user_email,
                "name": user_name
            }
        })

    except ValueError:
        return jsonify({"success": False, "message": "Token inválido"}), 400

@app.route('/backups', methods=['GET'])
def list_backups():
    """Lista los respaldos de una tabla."""
    db = request.args.get('db')
    table = request.args.get('table')
    backup_dir = os.path.join(DATA_DIR, db, "backups")
    if not os.path.exists(backup_dir):
        return jsonify({'backups': []})
    files = [f for f in os.listdir(backup_dir) if f.startswith(table)]
    return jsonify({'backups': files})

@app.route('/restore_backup', methods=['POST'])
def restore_backup():
    """Restaura un respaldo de una tabla."""
    data = request.json
    db = data.get('db')
    table = data.get('table')
    backup_file = data.get('backup_file')
    backup_path = os.path.join(DATA_DIR, db, "backups", backup_file)
    if not os.path.exists(backup_path):
        return jsonify({'error': 'Backup no encontrado'}), 404
    with open(backup_path, "r") as f:
        backup_data = json.load(f)
    save_table(db, table, backup_data)
    return jsonify({'message': f'Respaldo restaurado para {table} en {db}'})

@app.route('/databases', methods=['GET'])
def list_databases():
    """Lista todas las bases de datos."""
    dbs = [d for d in os.listdir(DATA_DIR) if os.path.isdir(os.path.join(DATA_DIR, d))]
    return jsonify({'databases': dbs})

@app.route('/drop_database', methods=['POST'])
def drop_database():
    """Elimina una base de datos y todas sus tablas."""
    data = request.json
    db = data.get('db')
    db_path = os.path.join(DATA_DIR, db)
    if not db or not is_valid_name(db):
        return jsonify({'error': 'Nombre de base de datos inválido'}), 400
    if not os.path.exists(db_path):
        return jsonify({'error': f'La base de datos {db} no existe'}), 400
    shutil.rmtree(db_path)
    query_cache.clear()
    return jsonify({'message': f'Base de datos {db} eliminada'})

@app.route('/tables', methods=['GET'])
def list_tables():
    """Lista todas las tablas de una base de datos."""
    db = request.args.get('db')
    db_path = os.path.join(DATA_DIR, db)
    if not db or not is_valid_name(db):
        return jsonify({'error': 'Nombre de base de datos inválido'}), 400
    if not os.path.exists(db_path):
        return jsonify({'error': f'La base de datos {db} no existe'}), 400
    tables = [f[:-5] for f in os.listdir(db_path) if f.endswith('.json') and f != "backups"]
    return jsonify({'tables': tables})

@app.route('/columns', methods=['GET'])
def get_columns():
    db = request.args.get('db')
    table = request.args.get('table')
    if not db or not table:
        return jsonify({'error': 'Faltan parámetros'}), 400
    table_data = load_table(db, table)
    if not table_data or "columns" not in table_data:
        return jsonify({'error': 'Tabla no encontrada'}), 404
    return jsonify({'columns': table_data["columns"]})

# ==========================
# ENDPOINT DE REGISTRO DE USUARIO
# ==========================
USERS_FILE = os.path.join(os.path.dirname(__file__), 'users.json')

@app.route('/register', methods=['POST'])
def register():
    data = request.get_json()
    username = data.get('username', '').strip().lower()
    password = data.get('password', '').strip()
    if not username or not password:
        return jsonify({'success': False, 'error': 'Usuario y contraseña requeridos'}), 400
    if os.path.exists(USERS_FILE):
        with open(USERS_FILE, 'r', encoding='utf-8') as f:
            try:
                users = json.load(f)
            except Exception:
                users = {}
    else:
        users = {}
    if username in users:
        return jsonify({'success': False, 'error': 'El usuario ya existe'}), 400
    users[username] = password
    with open(USERS_FILE, 'w', encoding='utf-8') as f:
        json.dump(users, f, ensure_ascii=False, indent=2)
    return jsonify({'success': True}), 200

@app.route('/upload_csv', methods=['POST'])
def upload_csv():
    """Carga datos desde un archivo CSV a una tabla de una base de datos."""
    db = request.form.get('db')
    table = request.form.get('table')
    file = request.files.get('file')
    if not db or not table or not file:
        return jsonify({'error': 'Falta el nombre de la base, tabla o el archivo'}), 400

    db_path = os.path.join(DATA_DIR, db)
    if not os.path.exists(db_path):
        os.makedirs(db_path)  # Crea la base si no existe

    table_path = os.path.join(db_path, f"{table}.json")
    if os.path.exists(table_path):
        table_data = load_table(db, table)
    else:
        # Si la tabla no existe, crea una nueva con columnas del CSV (tipo VARCHAR por defecto)
        reader = csv.DictReader(StringIO(file.read().decode('utf-8')))
        columns = reader.fieldnames
        table_data = {
            "columns": [{"name": col, "type": "VARCHAR(255)"} for col in columns],
            "rows": []
        }
        file.seek(0)  # Regresa el puntero para volver a leer

    reader = csv.DictReader(StringIO(file.read().decode('utf-8')))
    count = 0
    for row in reader:
        filtered_row = {col["name"]: row[col["name"]] for col in table_data["columns"] if col["name"] in row}
        table_data["rows"].append(filtered_row)
        count += 1
    save_table(db, table, table_data)
    return jsonify({'message': f'{count} filas agregadas a {table} en {db} desde CSV'})


@app.route('/health', methods=['GET'])
def health():
    """Endpoint de salud para verificar si el backend está corriendo."""
    return jsonify({'status': 'ok'})

# ==========================
# INICIO DE LA APP
# ==========================
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
