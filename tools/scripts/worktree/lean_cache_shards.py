"""Plan stable Actions cache groups from Lean imports and prior dev PRs."""

from __future__ import annotations

from collections import Counter, defaultdict
from graphlib import TopologicalSorter
import hashlib
import json
from pathlib import Path
import re
import subprocess

from lean_artifact_inventory import import_closure, project_imports, workspace_modules

HISTORY_COMMITS = 2000
MODULES_PER_SHARD = 4
SHARDS_PER_KEY = 8
PR_SUBJECT = re.compile(r"(?:^Merge pull request #[1-9][0-9]* from |\(#[1-9][0-9]*\)$)")


def reverse_edges(graph):
    users = {name: set() for name in graph}
    for name, dependencies in graph.items():
        for dependency in dependencies:
            users[dependency].add(name)
    return users


def logical_shards(modules, graph, users):
    terminals = sorted(name for name, parents in users.items() if not parents)
    signatures = {name: 1 << ordinal for ordinal, name in enumerate(terminals)}
    for name in reversed(tuple(TopologicalSorter(graph).static_order())):
        signature = signatures.get(name, 0)
        for user in users[name]:
            signature |= signatures[user]
        signatures[name] = signature

    edges = sorted((len(users[dep]), len(dependencies), name, dep)
                   for name, dependencies in graph.items() for dep in dependencies
                   if modules[name].package == modules[dep].package and signatures[name] == signatures[dep])
    parent = {name: name for name in modules}
    size = Counter({name: 1 for name in modules})

    def representative(name):
        while parent[name] != name:
            parent[name] = parent[parent[name]]
            name = parent[name]
        return name

    for _, _, user, dependency in edges:
        left, right = representative(user), representative(dependency)
        if left != right and size[left] + size[right] <= MODULES_PER_SHARD:
            parent[right] = left
            size[left] += size[right]
    shards = defaultdict(list)
    for name in sorted(modules):
        shards[representative(name)].append(name)
    return sorted(tuple(names) for names in shards.values())


def historical_changes(root, anchor, modules):
    """Read first-parent integration diffs from the fixed dev history anchor."""
    sources = {module.source.as_posix(): name for name, module in modules.items()}
    history = subprocess.run(
        ["git", "log", "--first-parent", "--diff-merges=first-parent", "--no-renames",
         "--format=%x1e%s%x00", "--name-only", "-z", f"-n{HISTORY_COMMITS}", anchor, "--"],
        cwd=root, check=True, stdout=subprocess.PIPE, text=True,
    ).stdout
    for record in history.split("\x1e")[1:]:
        subject, _, diff = record.partition("\0")
        if not PR_SUBJECT.search(subject):
            continue
        paths = {path.lstrip("\n") for path in diff.split("\0") if path}
        if any(Path(path).name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
               for path in paths):
            continue
        changed = {sources[path] for path in paths & sources.keys()}
        if changed:
            yield changed


def history_marks(shards, graph, users, changes):
    owner = {name: index for index, shard in enumerate(shards) for name in shard}
    marks = [set() for _ in shards]
    for ordinal, changed in enumerate(changes):
        for direction, edges in enumerate((graph, users)):
            for index in {owner[name] for name in import_closure(edges, changed)}:
                marks[index].add(ordinal * 2 + direction)
    return marks


def cache_groups(modules, shards, marks):
    by_package = defaultdict(list)
    for index, shard in enumerate(shards):
        by_package[modules[shard[0]].package].append(index)
    for indices in by_package.values():
        by_mark = defaultdict(set)
        for index in indices:
            for mark in marks[index]:
                by_mark[mark].add(index)
        remaining = set(indices)
        unseen = sorted((index for index in indices if not marks[index]),
                        key=shards.__getitem__)
        for index in sorted(indices, key=lambda item: (-len(marks[item]), shards[item])):
            if index not in remaining or not marks[index]:
                continue
            candidates = Counter()
            for mark in marks[index]:
                candidates.update(by_mark[mark] & remaining)
            candidates.pop(index)
            neighbors = []
            for other, overlap in candidates.items():
                union = len(marks[index]) + len(marks[other]) - overlap
                if overlap * 2 >= union:
                    neighbors.append((overlap / union, shards[other], other))
            chosen = [index, *(row[2] for row in sorted(neighbors, key=lambda row: (-row[0], row[1]))
                              [:SHARDS_PER_KEY - 1])]
            remaining.difference_update(chosen)
            yield tuple(sorted(shards[member] for member in chosen))
        for index in range(0, len(unseen), SHARDS_PER_KEY):
            yield tuple(shards[member] for member in unseen[index:index + SHARDS_PER_KEY])


def make_layout(root, anchor, modules, graph):
    users = reverse_edges(graph)
    logical = logical_shards(modules, graph, users)
    marks = history_marks(logical, graph, users, historical_changes(root, anchor, modules))
    return sorted(cache_groups(modules, logical, marks))


def group_identity(group):
    data = json.dumps(group, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(data).hexdigest()


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--anchor", required=True, help="immutable dev first-parent history anchor")
    args = parser.parse_args()
    if not re.fullmatch("[0-9a-f]{40}", args.anchor):
        parser.error("--anchor requires a complete commit SHA")
    modules = workspace_modules(args.repository)
    graph = project_imports(args.repository, modules)
    layout = make_layout(args.repository, args.anchor, modules, graph)
    print(json.dumps({group_identity(group): group for group in layout}, separators=(",", ":")))
