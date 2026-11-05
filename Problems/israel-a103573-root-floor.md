---
slug: israel-a103573-root-floor
bibkey: israel2026a103573
doi: null
url: https://oeis.org/A103573/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/IsraelA103573RootFloor.result
---

# Israel's A103573 root-difference conjecture

For every nonnegative integer n, let a(n) be the least nonnegative integer k
whose ordinary integer floor of sqrt(k)-k^(1/3) equals n. The conjecture places
a(n) at ceil(T(n)) or ceil(T(n))+1, with
T(n)=n^2+2*n^(5/3)+(7/3)*n^(4/3)+2*n+(110/81)*n^(2/3)+(182/243)*n^(1/3).
All powers are real powers of nonnegative bases. Source existence and leastness
are included, and no positive-index or eventual restriction replaces the target.

| Source clause | Lean definition or declaration |
| --- | --- |
| Ordinary real square and cube roots | `f` |
| Original rational real powers and coefficients | `T` |
| Every natural index, integer floor and least natural candidate | `IsSourceSequence` |
| Source existence and every source sequence's two-ceiling formula | `claim`, `result` |
| Zero index | `candidate`, zero branch |

The mathematical route uses the strictly increasing polynomial t^3-t^2 on
t>=1 and an exact polynomial sign certificate for the inverse threshold.
All auxiliary lemmas have actual consumers in the final theorem's proof.
Their preliminary proof shape is bind-only; no auxiliary escape witness or
separate solved-problem credit is asserted. The candidate admission basis for
the entire theorem is external open-problem resolution, subject to dependency
admission and independent source and proof review. This dossier asserts no
freeze, independent review, novelty certification, or solved-problem count.
The bounded prior-art screen remains partial; the unsuccessful global query
provides no negative result.

The four-slot source registration is unfinished under
[issue #26804](https://github.com/the-omega-institute/trureturing/issues/26804).
The complete source reconstruction, enrolled-template application, equivalence
bridge, whole-family variation and sensitivity, actual observational dependence,
and current binding evidence remain missing. No validated registration is claimed.
