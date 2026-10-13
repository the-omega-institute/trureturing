# Periodic integer predicates and finite residues

## Abstract

A positive period reduces integer existence with bounds to finite residue tests.

P is an arbitrary predicate on integers; no decision procedure for P is assumed in these arithmetic theorems. The period m is a positive natural number, and P(x+m) iff P(x) holds for every integer x. periodic_shift_of_mod extends this law to every integer multiple of m, using positive and negative induction.

periodic_interval states that a P-point in [lo,hi] exists exactly when some k<m satisfies lo+k<=hi and P(lo+k). Division with remainder moves a point down into the first period after lo, preserving P and the upper bound. periodic_has_residue instead moves a point into [0,m). A nonempty residue can be shifted above every finite list of lower bounds or below every finite list of upper bounds.

Here members(los) and members(his) mean list membership, and cast embeds naturals into integers. maxFrom and minFrom retain the starting integer as well as the list; their comparison and membership lemmas let the proof choose an extremal endpoint. The finite criterion combines these facts, including empty bound lists.

**Theorem 1.1 (One-sided and two-sided finite criterion).**

$$\forall P \in Int \to Prop,\; \forall m \in Nat,\; (0 < m) \implies ((\forall x \in Int,\; (\operatorname{P}\left(x + \operatorname{cast}\left(m\right)\right)) \iff (\operatorname{P}\left(x\right))) \implies (\forall los \in \operatorname{List}\left(Int\right),\; \forall his \in \operatorname{List}\left(Int\right),\; (\exists x \in Int,\; (\forall l \in \operatorname{members}\left(los\right),\; l \leq x) \land ((\forall h \in \operatorname{members}\left(his\right),\; x \leq h) \land (\operatorname{P}\left(x\right)))) \iff (\operatorname{if}\left(\operatorname{or}\left(\operatorname{isEmpty}\left(los\right), \operatorname{isEmpty}\left(his\right)\right), \exists k \in Nat,\; (k < m) \land (\operatorname{P}\left(\operatorname{cast}\left(k\right)\right)), \forall l \in \operatorname{members}\left(los\right),\; \forall h \in \operatorname{members}\left(his\right),\; \exists k \in Nat,\; (k < m) \land ((l + \operatorname{cast}\left(k\right) \leq h) \land (\operatorname{P}\left(l + \operatorname{cast}\left(k\right)\right)))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/PresburgerCooper.cooper_finite_criterion` (`✓ std3`). ∎

*Citation.* Vladimir Reshetnikov (2026). *ProveIt executable integer Presburger arithmetic*. URL: <https://github.com/VladimirReshetnikov/ProveIt/tree/ec9ab2ffd49f8861022d6f3d4c30205545a3386d/Logic/PresburgerArithmetic/Lean/PresburgerArithmetic>.

*Commentary.*

If either bound list is empty, it suffices to check one full set of residues. Otherwise each lower/upper pair must admit a residue-offset point. For the reverse implication, take the greatest lower bound and least upper bound; their pair supplies a common feasible point. This is a semantic reduction, not a complexity estimate.

## References

- Truth anchor: `D5/S0/Computability/PresburgerCooper.cooper_finite_criterion`
- Dependency: [D5/S0/Computability/PresburgerSyntax](PresburgerSyntax.md)
