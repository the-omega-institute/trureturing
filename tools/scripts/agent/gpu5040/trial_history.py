#!/usr/bin/env python3
"""Compact SQLite trial history. Querying requires only Python's standard library."""

import argparse
import json
from pathlib import Path
import sqlite3
import sys

from search_config import canonical, identity, scientific_without_runtime
from state_store import default_history, external_path, utc_now


DDL = """
CREATE TABLE IF NOT EXISTS trials (
 identity TEXT PRIMARY KEY, descriptor TEXT NOT NULL UNIQUE,
 status TEXT NOT NULL CHECK(status IN ('running','interrupted','failed','completed')),
 state_directory TEXT NOT NULL, iteration INTEGER NOT NULL DEFAULT 0,
 summary TEXT NOT NULL, candidate_sha256 TEXT, provenance TEXT NOT NULL,
 created_utc TEXT NOT NULL, updated_utc TEXT NOT NULL, error TEXT
);
CREATE TABLE IF NOT EXISTS champions (
 dimension INTEGER PRIMARY KEY, candidate_sha256 TEXT NOT NULL,
 metrics TEXT NOT NULL, checkpoint_path TEXT NOT NULL, updated_utc TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS verifications (
 candidate_sha256 TEXT PRIMARY KEY,
 status TEXT NOT NULL CHECK(status IN ('running','failed','verified')),
 result TEXT, updated_utc TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS legacy_imports (
 lineage TEXT PRIMARY KEY, evidence TEXT NOT NULL, output_directory TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS legacy_exclusions (
 lineage TEXT NOT NULL REFERENCES legacy_imports(lineage), scientific_identity TEXT NOT NULL,
 trial_identity TEXT NOT NULL REFERENCES trials(identity),
 PRIMARY KEY(lineage, scientific_identity)
);
"""


def empty_summary(best_complete=True):
    return {"initial": None, "final": None, "best": None, "best_complete": best_complete}


class Registry:
    def __init__(self, path):
        self.path = external_path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.connection = sqlite3.connect(str(self.path), timeout=30)
        try:
            if self.connection.execute("PRAGMA user_version").fetchone()[0] not in (0, 1):
                raise ValueError("unsupported history schema")
            self.connection.execute("PRAGMA foreign_keys=ON")
            self.connection.execute("PRAGMA journal_mode=DELETE")
            self.connection.execute("PRAGMA synchronous=EXTRA")
            self.connection.executescript(DDL)
            self.connection.execute("PRAGMA user_version=1")
            self.connection.commit()
        except BaseException:
            self.close()
            raise

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.close()

    def close(self):
        self.connection.close()

    def get(self, key):
        cursor = self.connection.execute("SELECT * FROM trials WHERE identity=?", (key,))
        row = cursor.fetchone()
        return decode(cursor, row) if row else None

    def rows(self):
        cursor = self.connection.execute("SELECT * FROM trials ORDER BY created_utc, rowid")
        return [decode(cursor, row) for row in cursor]

    def completed(self, desc):
        row = self.get(identity(desc))
        return row is not None and row["status"] == "completed"

    def claim(self, desc, directory, provenance):
        key, owner = identity(desc), str(Path(directory).resolve())
        with self.connection:
            self.connection.execute("BEGIN IMMEDIATE")
            row = self.get(key)
            if row:
                if row["descriptor"] != desc:
                    raise ValueError("trial identity collision")
                if row["status"] == "completed":
                    raise ValueError("completed trial must be skipped before initialization")
                if row["state_directory"] != owner:
                    raise ValueError("trial owned by another state; retry --state-dir "
                                     + row["state_directory"] + " with the same scientific configuration; "
                                     "use --resume when latest.pt exists")
                self.connection.execute("UPDATE trials SET status='running', provenance=?, "
                                        "updated_utc=?, error=NULL WHERE identity=?",
                                        (canonical(provenance), utc_now(), key))
            else:
                now = utc_now()
                self.connection.execute("INSERT INTO trials VALUES (?,?,?,?,?,?,?,?,?,?,?)", (
                    key, canonical(desc), "running", owner, 0, canonical(empty_summary()), None,
                    canonical(provenance), now, now, None))
        return key

    def mark(self, key, status, iteration=None, summary=None, error=None):
        if status not in ("running", "interrupted", "failed"):
            raise ValueError("completion requires a terminal checkpoint")
        row = self.get(key)
        if not row or row["status"] == "completed":
            return
        with self.connection:
            self.connection.execute("UPDATE trials SET status=?, iteration=?, summary=?, error=?, "
                                    "updated_utc=? WHERE identity=? AND status!='completed'", (
                status, row["iteration"] if iteration is None else iteration,
                canonical(row["summary"] if summary is None else summary), error, utc_now(), key))

    def complete(self, key, iteration, summary, candidate_sha256):
        row = self.get(key)
        if not row or iteration != row["descriptor"]["budget"]:
            raise ValueError("completion iteration must equal the full trial budget")
        with self.connection:
            if row["status"] == "completed":
                if (row["iteration"], row["summary"], row["candidate_sha256"]) != (
                        iteration, summary, candidate_sha256):
                    raise ValueError("conflicting terminal completion evidence")
                return
            self.connection.execute("UPDATE trials SET status='completed', iteration=?, summary=?, "
                                    "candidate_sha256=?, updated_utc=?, error=NULL WHERE identity=?", (
                iteration, canonical(summary), candidate_sha256, utc_now(), key))

    def champion(self, dimension, digest, metrics, path):
        with self.connection:
            row = self.connection.execute("SELECT metrics FROM champions WHERE dimension=?", (dimension,)).fetchone()
            if row and json.loads(row[0])["fidelity"] >= metrics["fidelity"]:
                return
            self.connection.execute("INSERT OR REPLACE INTO champions VALUES (?,?,?,?,?)", (
                dimension, digest, canonical(metrics), path, utc_now()))

    def champions(self):
        cursor = self.connection.execute("SELECT * FROM champions ORDER BY dimension")
        return [decode(cursor, row) for row in cursor]

    def verification(self, digest, status, result=None):
        with self.connection:
            self.connection.execute("INSERT OR REPLACE INTO verifications VALUES (?,?,?,?)", (
                digest, status, canonical(result) if result is not None else None, utc_now()))

    def verifications(self, digest=None):
        cursor = self.connection.execute("SELECT * FROM verifications" + (
            " WHERE candidate_sha256=?" if digest else ""), (digest,) if digest else ())
        return [decode(cursor, row) for row in cursor]

    def add_lineage(self, lineage, evidence, directory):
        row = self.connection.execute("SELECT evidence, output_directory FROM legacy_imports WHERE lineage=?",
                                      (lineage,)).fetchone()
        values = (canonical(evidence), str(directory))
        if row and row != values:
            raise ValueError("lineage already imported with different evidence or output directory")
        with self.connection:
            self.connection.execute("INSERT OR IGNORE INTO legacy_imports VALUES (?,?,?)", (lineage, *values))

    def require_lineage(self, lineage):
        if lineage and not self.connection.execute("SELECT 1 FROM legacy_imports WHERE lineage=?", (lineage,)).fetchone():
            raise ValueError("unknown --legacy-lineage; convert retained evidence first")

    def exclude(self, lineage, desc, trial_key):
        row = self.get(trial_key)
        if not row or row["status"] != "completed":
            raise ValueError("only completed legacy evidence can exclude a trial")
        with self.connection:
            self.connection.execute("INSERT OR IGNORE INTO legacy_exclusions VALUES (?,?,?)", (
                lineage, identity(scientific_without_runtime(desc)), trial_key))

    def excluded(self, lineage, desc):
        if not lineage:
            return False
        return self.connection.execute("SELECT 1 FROM legacy_exclusions WHERE lineage=? AND scientific_identity=?",
            (lineage, identity(scientific_without_runtime(desc)))).fetchone() is not None


def decode(cursor, row):
    result = dict(zip((item[0] for item in cursor.description), row))
    for key in ("descriptor", "summary", "provenance", "metrics", "result", "evidence"):
        if key in result and result[key] is not None:
            result[key] = json.loads(result[key])
    return result


def query(path, status=None, dimension=None, limit=100):
    path = external_path(path)
    if not path.exists():
        return {"history_db": str(path), "trials": [], "champions": [], "verifications": [], "legacy_imports": []}
    connection = sqlite3.connect(path.as_uri() + "?mode=ro", uri=True, timeout=30)
    try:
        if connection.execute("PRAGMA user_version").fetchone()[0] != 1:
            raise ValueError("unsupported history schema")
        result = {"history_db": str(path)}
        for table in ("trials", "champions", "verifications", "legacy_imports"):
            conditions, params = [], []
            if table == "trials":
                if status:
                    conditions.append("status=?")
                    params.append(status)
                if dimension is not None:
                    # SQLite JSON extensions are not a prerequisite.
                    conditions.append("descriptor LIKE ?")
                    params.append('%"dimension":' + str(dimension) + ',%')
            sql = "SELECT * FROM " + table + (" WHERE " + " AND ".join(conditions) if conditions else "")
            cursor = connection.execute(sql + " ORDER BY rowid DESC LIMIT ?", (*params, limit))
            result[table] = [decode(cursor, row) for row in cursor]
        return result
    finally:
        connection.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--history-db", default=str(default_history()))
    parser.add_argument("--status", choices=("running", "interrupted", "failed", "completed"))
    parser.add_argument("--dimension", type=int)
    parser.add_argument("--limit", type=int, default=100)
    args = parser.parse_args(argv)
    try:
        if args.limit <= 0:
            raise ValueError("limit must be positive")
        print(json.dumps(query(args.history_db, args.status, args.dimension, args.limit), indent=2, allow_nan=False))
        return 0
    except (ValueError, OSError, sqlite3.Error) as error:
        print("history error: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
