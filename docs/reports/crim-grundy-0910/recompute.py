"""Two independently implemented CRIM computations; no supplied SG table is input."""
import json
from functools import cache
from pathlib import Path

root = (6, 6, 5, 4, 3, 2, 1)

# Method A: literal conjugate / delete a row / conjugate back; recursive mex.
def conjugate(p):
    return tuple(sum(x >= j for x in p) for j in range(1, max(p, default=0)+1))

def moves_a(p):
    q = conjugate(p)
    return set(p[:i]+p[i+1:] for i in range(len(p))) | set(
        conjugate(q[:j]+q[j+1:]) for j in range(len(q)))

visited_a = {}
@cache
def recursive(p):
    options = moves_a(p)
    values = {recursive(q) for q in options}
    value = 0
    while value in values:
        value += 1
    visited_a[p] = options
    return value

answer_a = recursive(root)

# Method B: direct coordinate deletion in the Young diagram, no conjugation,
# explicit graph construction followed by topological evaluation by area.
def moves_b(p):
    result = set()
    for i in range(len(p)):
        result.add(tuple(x for j, x in enumerate(p) if j != i))
    for j in range(p[0] if p else 0):
        lengths = [x - int(j < x) for x in p]
        result.add(tuple(x for x in lengths if x != 0))
    return result

graph = {}
work = [root]
while work:
    p = work.pop()
    if p in graph:
        continue
    graph[p] = moves_b(p)
    work.extend(graph[p] - graph.keys())

values_b, depth, edges = {}, {}, 0
ordered = sorted(graph, key=lambda p: (sum(p), p))
for p in ordered:
    options = graph[p]
    assert all(sum(q) < sum(p) for q in options)
    used = [values_b[q] for q in options]
    # Independent mex implementation: membership vector and first absent index.
    present = [False] * (len(options)+1)
    for v in used:
        if v < len(present):
            present[v] = True
    values_b[p] = present.index(False)
    depth[p] = 0 if not options else 1 + max(depth[q] for q in options)
    edges += len(options)

assert graph == visited_a
assert all(recursive(p) == values_b[p] for p in graph)
report = dict(root=root, cells=sum(root), method_a_value=answer_a,
              method_b_value=values_b[root], states_a=len(visited_a),
              states_b=len(graph), edges=edges, max_depth_edges=depth[root],
              successors=[dict(partition=p, a=recursive(p), b=values_b[p])
                          for p in sorted(graph[root], reverse=True)],
              dag=[dict(partition=p, grundy=values_b[p], depth=depth[p],
                        options=sorted(graph[p])) for p in ordered])
if __name__ == "__main__":
    import sys
    Path(sys.argv[1]).write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k:v for k,v in report.items() if k != "dag"}, indent=2))
