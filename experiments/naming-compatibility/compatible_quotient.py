"""Least operation-compatible identification on a finite common state space.

The algorithm implements classical unary congruence closure. Its independent
replay checker verifies finite results; it is not a Lean certificate.
License: Apache-2.0, as specified by the repository LICENSE.
"""

from collections import deque
import argparse
import json
from pathlib import Path
import sys


def validate(model):
    n = model["states"]
    if type(n) is not int or n < 1:
        raise ValueError("states must be a positive integer")
    for field in ("identifications", "operations"):
        if not isinstance(model[field], dict):
            raise ValueError(f"{field} must be a name-to-map object")
        for name, mapping in model[field].items():
            if not isinstance(name, str) or not name:
                raise ValueError("map names must be nonempty strings")
            if not isinstance(mapping, list) or len(mapping) != n or any(type(x) is not int or not 0 <= x < n
                                        for x in mapping):
                raise ValueError(f"{name} must be a total map on the common states")
            if field == "identifications" and sorted(mapping) != list(range(n)):
                raise ValueError(f"{name} must be a permutation")
    if not isinstance(model["target"], list) or len(model["target"]) != n or any(not isinstance(x, str)
                                      for x in model["target"]):
        raise ValueError("target must give one string label per state")


def components(adjacency):
    """Graph traversal, independent of the solver's union-find."""
    labels = [-1] * len(adjacency)
    blocks = []
    for start in range(len(adjacency)):
        if labels[start] >= 0:
            continue
        label = len(blocks)
        labels[start] = label
        block, todo = [], [start]
        while todo:
            x = todo.pop()
            block.append(x)
            for y in adjacency[x]:
                if labels[y] < 0:
                    labels[y] = label
                    todo.append(y)
        blocks.append(sorted(block))
    return labels, blocks


def target_constant(blocks, target):
    return all(len({target[x] for x in block}) == 1 for block in blocks)


def replay(model, result):
    """Check justified merge edges, their partition, and complete stability."""
    validate(model)
    n = model["states"]
    graph = [set() for _ in range(n)]
    accepted = []
    for edge in result["merges"]:
        x, y = edge["pair"]
        if any(type(z) is not int or not 0 <= z < n for z in (x, y)):
            raise ValueError("merge endpoint outside the common state space")
        reason = edge["reason"]
        if reason["kind"] == "identification":
            mapping = model["identifications"][reason["name"]]
            if mapping[x] != y:
                raise ValueError("unjustified identification edge")
        elif reason["kind"] == "operation":
            parent = reason["parent"]
            if type(parent) is not int or not 0 <= parent < len(accepted):
                raise ValueError("operation edge requires an earlier parent")
            a, b = accepted[parent]
            mapping = model["operations"][reason["name"]]
            if (mapping[a], mapping[b]) != (x, y):
                raise ValueError("unjustified operation edge")
        else:
            raise ValueError("unknown merge reason")
        graph[x].add(y)
        graph[y].add(x)
        accepted.append((x, y))
    labels, blocks = components(graph)
    if result["blocks"] != blocks:
        raise ValueError("reported partition differs from justified edges")
    for mapping in model["identifications"].values():
        if any(labels[x] != labels[mapping[x]] for x in range(n)):
            raise ValueError("partition misses an initial identification")
    transitions = {}
    for name, mapping in model["operations"].items():
        row = []
        for block in blocks:
            images = {labels[mapping[x]] for x in block}
            if len(images) != 1:
                raise ValueError("operation is not well defined on a block")
            row.append(images.pop())
        transitions[name] = row
    if result["descended_operations"] != transitions:
        raise ValueError("incorrect descended operation table")
    initial_graph = [set() for _ in range(n)]
    for mapping in model["identifications"].values():
        for x, y in enumerate(mapping):
            initial_graph[x].add(y)
            initial_graph[y].add(x)
    _, initial = components(initial_graph)
    if result["initial_blocks"] != initial:
        raise ValueError("incorrect initial partition")
    for field, partition in (("initial_target_recoverable", initial),
                             ("compatible_target_recoverable", blocks)):
        if type(result[field]) is not bool or result[field] != target_constant(
                partition, model["target"]):
            raise ValueError("incorrect target recovery claim")
    obstruction = result["obstruction"]
    if obstruction is None:
        if not result["compatible_target_recoverable"]:
            raise ValueError("missing target obstruction")
    else:
        x, y = obstruction["pair"]
        if any(type(z) is not int or not 0 <= z < n for z in (x, y)):
            raise ValueError("obstruction endpoint outside the state space")
        if (labels[x] != labels[y] or model["target"][x] == model["target"][y]
                or obstruction["target"] != [model["target"][x], model["target"][y]]):
            raise ValueError("incorrect target obstruction")
        cursor = x
        for index in obstruction["merge_path"]:
            if type(index) is not int or not 0 <= index < len(accepted):
                raise ValueError("invalid obstruction path index")
            a, b = accepted[index]
            if cursor not in (a, b):
                raise ValueError("disconnected obstruction path")
            cursor = b if cursor == a else a
        if cursor != y:
            raise ValueError("obstruction path does not reach its endpoint")
    return labels, blocks


def solve(model):
    validate(model)
    n = model["states"]
    parent, size = list(range(n)), [1] * n
    edges, todo = [], deque()

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def merge(x, y, reason):
        a, b = root(x), root(y)
        if a == b:
            return
        if size[a] < size[b]:
            a, b = b, a
        parent[b], size[a] = a, size[a] + size[b]
        todo.append(len(edges))
        edges.append({"pair": [x, y], "reason": reason})

    for name, mapping in model["identifications"].items():
        for x, y in enumerate(mapping):
            merge(x, y, {"kind": "identification", "name": name})
    initial_graph = [set() for _ in range(n)]
    for edge in edges:
        x, y = edge["pair"]
        initial_graph[x].add(y)
        initial_graph[y].add(x)
    _, initial = components(initial_graph)
    while todo:
        index = todo.popleft()
        x, y = edges[index]["pair"]
        for name, mapping in model["operations"].items():
            merge(mapping[x], mapping[y],
                  {"kind": "operation", "name": name, "parent": index})
    graph = [set() for _ in range(n)]
    edge_at = {}
    for index, edge in enumerate(edges):
        x, y = edge["pair"]
        graph[x].add(y)
        graph[y].add(x)
        edge_at[x, y] = edge_at[y, x] = index
    labels, blocks = components(graph)
    transitions = {name: [labels[mapping[block[0]]] for block in blocks]
                   for name, mapping in model["operations"].items()}
    obstruction = None
    for block in blocks:
        x = block[0]
        different = [y for y in block if model["target"][y] != model["target"][x]]
        if not different:
            continue
        y = different[0]
        previous, search = {x: None}, deque([x])
        while y not in previous:
            z = search.popleft()
            for w in sorted(graph[z]):
                if w not in previous:
                    previous[w] = z
                    search.append(w)
        path, cursor = [], y
        while previous[cursor] is not None:
            before = previous[cursor]
            path.append(edge_at[before, cursor])
            cursor = before
        obstruction = {"pair": [x, y], "target": [model["target"][x],
                       model["target"][y]], "merge_path": list(reversed(path))}
        break
    result = {"initial_blocks": initial, "blocks": blocks, "merges": edges,
              "descended_operations": transitions,
              "initial_target_recoverable": target_constant(initial, model["target"]),
              "compatible_target_recoverable": target_constant(blocks, model["target"]),
              "obstruction": obstruction}
    replay(model, result)
    return result


def examples():
    strict = {"states": 3, "identifications": {"swap": [1, 0, 2]},
              "operations": {"update": [0, 2, 2]}, "target": ["a", "a", "b"]}
    equivariant = {**strict, "operations": {"identity": [0, 1, 2]}}
    models = {"three_state_obstruction": strict, "compatible_control": equivariant}
    for modulus in (2, 3, 5, 7, 11):
        points = [(a, b) for a in range(modulus) for b in range(modulus)]
        index = {point: i for i, point in enumerate(points)}
        models[f"fib_signed_mod_{modulus}"] = {
            "states": len(points),
            "identifications": {"C": [index[-b % modulus, a] for a, b in points]},
            "operations": {"M": [index[b, (a + b) % modulus] for a, b in points]},
            "target": [str((a * a + b * b) % modulus) for a, b in points]}
    return models


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="one finite model as JSON")
    args = parser.parse_args()
    if args.input:
        model = json.loads(args.input.read_text())
        output = {"model": model, "result": solve(model)}
    else:
        output = {name: {"model": model, "result": solve(model)}
                  for name, model in examples().items()}
    json.dump(output, sys.stdout, ensure_ascii=False, indent=2, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
