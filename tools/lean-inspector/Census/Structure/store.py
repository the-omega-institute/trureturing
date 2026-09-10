"""Disk-backed declaration summaries and first-frozen-hit closure.

Only one module/one declaration is decoded at a time. Recursive helper work,
including SCC visited state and boundary provenance, lives in SQLite.
"""

import functools
import collections
import gzip
import hashlib
import json
import pathlib
import sqlite3
import zlib

from emission import parse_name_key
from incremental import atomic_json
from streaming import canonical, digest


def wire_key(key):
    return {"theorem_name": parse_name_key(key[1]), "statement_id": key[2]}


def compressed(value):
    return zlib.compress(canonical(value))


def decoded(value):
    return json.loads(zlib.decompress(value))


class Store:
    def __init__(self, path):
        self.path = pathlib.Path(path)
        self.db = sqlite3.connect(path)
        self.db.executescript("""
            PRAGMA cache_size=-8192;
            PRAGMA temp_store=FILE;
            CREATE TABLE IF NOT EXISTS modules
              (name TEXT PRIMARY KEY, imports TEXT, library TEXT, address TEXT, error TEXT);
            CREATE TABLE IF NOT EXISTS decl
              (module TEXT, name TEXT, kind TEXT, value BLOB, types BLOB, hash TEXT,
               PRIMARY KEY(module,name));
            CREATE INDEX IF NOT EXISTS names ON decl(name);
            CREATE TEMP TABLE todo(module TEXT,name TEXT,uncertain INTEGER,done INTEGER DEFAULT 0,
                                  PRIMARY KEY(module,name,uncertain));
            CREATE TEMP TABLE boundary(name TEXT,module TEXT,library TEXT,PRIMARY KEY(name,module));
            CREATE TEMP TABLE tokens(context TEXT,name TEXT,signature TEXT,PRIMARY KEY(context,name));
            CREATE TEMP TABLE scopes(module TEXT PRIMARY KEY,bits BLOB);
        """)
        self.dirty = set()
        self.frozen = {}
        self.graph = None
        self.module_indices = {}
        self.scope = functools.lru_cache(maxsize=32)(self._scope)
        self.owners = functools.lru_cache(maxsize=4096)(self._owners)

    def close(self):
        self.db.commit()
        self.db.close()

    def module(self, name, imports, library, address=None, error=None):
        self.db.execute("INSERT OR REPLACE INTO modules VALUES (?,?,?,?,?)",
                        (name, json.dumps(sorted(set(imports))), library, address, error))
        self.graph = None
        self.db.execute("DELETE FROM scopes")
        self.scope.cache_clear()
        self.owners.cache_clear()

    def remove_module(self, name):
        self.db.execute("DELETE FROM decl WHERE module=?", (name,))
        self.db.execute("DELETE FROM modules WHERE name=?", (name,))
        self.owners.cache_clear()
        self.scope.cache_clear()
        self.graph = None
        self.db.execute("DELETE FROM scopes")

    def declaration(self, module, name, kind, value, types=()):
        value = None if value is None else sorted(set(value))
        types = sorted(set(types))
        hashed = digest([kind, value, types])
        self.db.execute("INSERT OR REPLACE INTO decl VALUES (?,?,?,?,?,?)",
                        (module, name, kind, compressed(value), compressed(types), hashed))
        self.dirty.add(module)
        self.owners.cache_clear()

    def finish_module(self, module, address):
        self.db.execute("UPDATE modules SET address=? WHERE name=?", (address, module))
        self.dirty.discard(module)

    def snapshot(self):
        for module in sorted(self.dirty):
            hashed = hashlib.sha256()
            for row in self.db.execute("SELECT name,hash FROM decl WHERE module=? ORDER BY name", (module,)):
                hashed.update(canonical(row))
            self.finish_module(module, "sha256:" + hashed.hexdigest())
        self.db.commit()
        return digest(list(self.db.execute("SELECT * FROM modules ORDER BY name")))

    def set_frozen(self, keys):
        self.frozen = {}
        for key in keys:
            self.frozen.setdefault((key[0], key[1]), []).append(tuple(key))
        self.collision_names = {name for name, count in collections.Counter(k[1] for k in keys).items() if count > 1}

    def frozen_keys(self, module, name):
        return self.frozen.get((module, name), [])

    def _scope(self, module):
        if self.graph is None:
            self.graph = {m: json.loads(imports) for m, imports in
                          self.db.execute("SELECT name,imports FROM modules")}
            self.module_indices = {m: i for i, m in enumerate(sorted(self.graph))}
        cached = self.db.execute("SELECT bits FROM scopes WHERE module=?", (module,)).fetchone()
        if cached:
            return zlib.decompress(cached[0])
        visited, pending = set(), [module]
        while pending:
            owner = pending.pop()
            if owner in visited:
                continue
            if owner not in self.graph:
                raise ValueError("dependency_unresolved")
            visited.add(owner)
            pending.extend(self.graph[owner])
        # Import closures are disk-backed too. The small resident cache holds
        # 32 bit vectors, not 32 sets of all imported module names.
        bits = bytearray((len(self.module_indices) + 7) // 8)
        for owner in visited:
            index = self.module_indices[owner]
            bits[index // 8] |= 1 << (index % 8)
        encoded = bytes(bits)
        self.db.execute("INSERT INTO scopes VALUES (?,?)", (module, zlib.compress(encoded)))
        return encoded

    def _owners(self, name):
        return self.db.execute("""SELECT d.module,m.library,d.hash,m.error FROM decl d
            JOIN modules m ON m.name=d.module WHERE d.name=? ORDER BY d.module""", (name,)).fetchall()

    def signature(self, context, name):
        try:
            scope = self.scope(context)
        except ValueError:
            return []
        result = []
        for module, library, hashed, error in self.owners(name):
            index = self.module_indices[module]
            if not scope[index // 8] & (1 << (index % 8)):
                continue
            frozen = self.frozen_keys(module, name)
            # A frozen target's proof body does not affect a first-hit edge.
            result.append([module, library, [k[2] for k in frozen],
                           hashed if library == "repository" and not frozen else None, error])
        return result

    def raw(self, module, name):
        row = self.db.execute("SELECT kind,value,types,hash FROM decl WHERE module=? AND name=?",
                              (module, name)).fetchone()
        return (row[0], decoded(row[1]), decoded(row[2]), row[3]) if row else None

    def cache_valid(self, entry, token_path, key, policy, root_hash):
        if entry.get("root") != list(key) or entry.get("policy") != policy or entry.get("root_hash") != root_hash:
            return False
        hasher = hashlib.sha256(canonical([policy, root_hash]))
        with gzip.open(token_path, "rb") as tokens:
            for line in tokens:
                context, name, prior = json.loads(line)
                current = self.signature(context, name)
                if prior != current:
                    return False
                hasher.update(canonical([context, name, current]))
        return entry["cache_key"] == "sha256:" + hasher.hexdigest()

    def read_key(self, key, core, folder, policy):
        folder = pathlib.Path(folder)
        folder.mkdir(parents=True, exist_ok=True)
        address = digest([key[1], key[2]])[7:]
        entry_path = folder / (address + ".json")
        token_path = folder / (address + ".tokens.gz")
        frontier_path = folder / (address + ".frontier.gz")
        root = self.raw(key[0], key[1])
        root_state = self.db.execute("SELECT library,error FROM modules WHERE name=?", (key[0],)).fetchone()
        root_hash = digest([root[3] if root else None, root_state, self.frozen_keys(key[0], key[1])])
        if entry_path.is_file() and token_path.is_file() and frontier_path.is_file():
            entry = json.loads(entry_path.read_bytes())
            if self.cache_valid(entry, token_path, key, policy, root_hash):
                return entry, frontier_path, True
        entry = {"root": list(key), "root_hash": root_hash, "policy": policy,
                 "direct": [], "folded": [], "potential": [], "unbounded": False,
                 "value_constant_count": None, "core_or_frozen_support": "undetermined",
                 "empty_core_support": "undetermined", "reason": None,
                 "scope_resolved_direct_references": 0, "ambiguous_direct_references": 0}
        errors, direct, folded, potential = set(), set(), set(), set()
        for table in ("todo", "boundary", "tokens"):
            self.db.execute("DELETE FROM " + table)
        source_error = self.db.execute("SELECT error FROM modules WHERE name=?", (key[0],)).fetchone()
        if source_error is None or source_error[0]:
            errors.add(source_error[0] if source_error else "missing_olean_part")
        elif root is None:
            errors.add("constant_missing")
        elif root[0] != "theorem":
            errors.add("kind_mismatch")
        elif root[1] is None:
            errors.add("value_unavailable")
        elif len(self.frozen_keys(key[0], key[1])) != 1:
            errors.add("frozen_key_ambiguous")

        def consume(context, refs, seed=False, uncertain=False):
            supported = True
            for name in sorted(set(refs)):
                candidates = self.signature(context, name)
                self.db.execute("INSERT OR REPLACE INTO tokens VALUES (?,?,?)",
                                (context, name, json.dumps(candidates)))
                frozen_candidates = [(m, name, identity) for m, _, ids, _, _ in candidates for identity in ids]
                if len(candidates) == 1 and len(frozen_candidates) == 1 and not candidates[0][4]:
                    target = frozen_candidates[0][2]
                    (potential if uncertain else folded).add(target)
                    if seed:
                        direct.add(target)
                        entry["scope_resolved_direct_references"] += name in self.collision_names
                    continue
                if seed and name not in core:
                    supported = False
                if not candidates or any(c[4] for c in candidates):
                    errors.add("dependency_unresolved")
                    entry["unbounded"] = True
                elif frozen_candidates:
                    errors.add("frozen_key_ambiguous")
                    potential.update(k[2] for k in frozen_candidates)
                    entry["ambiguous_direct_references"] += seed
                    for module, library, ids, _, _ in candidates:
                        if library == "repository" and not ids:
                            self.db.execute("INSERT OR IGNORE INTO todo(module,name,uncertain) VALUES (?,?,1)",
                                            (module, name))
                elif all(c[1] != "repository" for c in candidates):
                    # A reserved upstream constant can be realized in several
                    # modules. Preserve ALL in-scope provenance, never pick one.
                    self.db.executemany("INSERT OR IGNORE INTO boundary VALUES (?,?,?)",
                                        [(name, c[0], c[1]) for c in candidates])
                elif len(candidates) == 1:
                    self.db.execute("INSERT OR IGNORE INTO todo(module,name,uncertain) VALUES (?,?,?)",
                                    (candidates[0][0], name, int(uncertain)))
                else:
                    errors.add("dependency_unresolved")
                    # Keep the root unavailable, but bound its unknown edges
                    # by all readable candidate bodies. Never select an owner
                    # or present their union as an exact prerequisite set.
                    for module, library, _, _, _ in candidates:
                        if library == "repository":
                            self.db.execute("INSERT OR IGNORE INTO todo(module,name,uncertain) VALUES (?,?,1)",
                                            (module, name))
            return supported

        if not errors:
            entry["value_constant_count"] = len(root[1])
            support = consume(key[0], root[1], seed=True)
            entry["core_or_frozen_support"] = True if support else "undetermined"
            entry["empty_core_support"] = True if root[1] and len(direct) == len(root[1]) else "undetermined"
            while True:
                todo = self.db.execute("SELECT module,name,uncertain FROM todo WHERE done=0 LIMIT 1").fetchone()
                if todo is None:
                    break
                self.db.execute("UPDATE todo SET done=1 WHERE module=? AND name=? AND uncertain=?", todo)
                helper = self.raw(*todo[:2])
                if helper is None:
                    errors.add("dependency_unresolved")
                    entry["unbounded"] = True
                elif helper[0] == "axiom":
                    pass
                elif helper[0] in ("def", "theorem", "opaque") and helper[1] is None:
                    errors.add("value_unavailable")
                    entry["unbounded"] = True
                else:
                    # Same dependency definition as Inspector; SCCs terminate
                    # through the disk visited set and all members are closed.
                    consume(todo[0], (helper[1] or []) + helper[2], uncertain=bool(todo[2]))
        else:
            entry["unbounded"] = True
        entry.update(direct=sorted(direct), folded=sorted(folded), potential=sorted(potential),
                     helper_visits=self.db.execute("SELECT count(*) FROM todo").fetchone()[0])
        if errors:
            order = ["missing_olean_part", "constant_missing", "kind_mismatch", "value_unavailable",
                     "dependency_unresolved", "frozen_key_ambiguous"]
            entry["reason"] = next(reason for reason in order if reason in errors)
        hasher = hashlib.sha256(canonical([policy, root_hash]))
        with gzip.open(token_path, "wb", compresslevel=1) as tokens:
            for context, name, signature in self.db.execute("SELECT * FROM tokens ORDER BY context,name"):
                line = canonical([context, name, json.loads(signature)])
                tokens.write(line)
                hasher.update(line)
        entry["cache_key"] = "sha256:" + hasher.hexdigest()
        # JSON lines are streamed later into each row's frontier array.
        with gzip.open(frontier_path, "wb", compresslevel=1) as frontier:
            current, provenance = None, []
            for name, module, library in self.db.execute("SELECT * FROM boundary ORDER BY name,module"):
                if current is not None and name != current:
                    frontier.write(canonical({"constant_name": parse_name_key(current), "provenance": provenance,
                                              "library": provenance[0]["library"] if len({p["library"] for p in provenance}) == 1 else None}))
                    provenance = []
                current = name
                provenance.append({"declaring_module": module, "library": library})
            if current is not None:
                frontier.write(canonical({"constant_name": parse_name_key(current), "provenance": provenance,
                                          "library": provenance[0]["library"] if len({p["library"] for p in provenance}) == 1 else None}))
        atomic_json(entry_path, entry)
        return entry, frontier_path, False
