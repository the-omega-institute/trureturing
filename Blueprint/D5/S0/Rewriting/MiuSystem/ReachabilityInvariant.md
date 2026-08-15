# MIU Reachability Invariant

## Abstract

MIU derivability has exactly two I-count residues modulo three and excludes MU.

**Theorem 1.1 (Reachable residues and MU exclusion).**

$$(\forall w\in \mathcal{W},\ \operatorname{Derivable}(w) \Rightarrow countI(w) \bmod 3 \neq 0) \land (\forall r\in \mathbb{N},\ ((\exists w\in \mathcal{W},\ \operatorname{Derivable}(w) \land countI(w) \bmod 3 = r) \iff r = 1 \lor r = 2)) \land \neg \operatorname{Derivable}(MU).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/MiuSystem/ReachabilityInvariant.miu_observation_invariant_clauses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem is stated directly over pinned mathlib's Miu.Miustr and Miu.Derivable notions. That archived development defines the MIU axiom and all four production rules.

The proof applies mathlib's necessary-condition theorem: every derivable word has I-count congruent to one or two modulo three. Thus the count is never zero modulo three, without any bounded enumeration.

Both residues occur: MI witnesses residue one, and one application of the tail-duplication rule derives MII and witnesses residue two. The final conjunct applies mathlib's theorem that MU is not derivable.

This result does not assert the separate bounded-BFS cardinality 216. Pure kernel evaluation of that finite computation exceeded the measured elaboration budget, while native evaluation would enlarge the permitted axiom closure, so that numerical clause remains open.

## References

- Truth anchor: `D5/S0/Rewriting/MiuSystem/ReachabilityInvariant.miu_observation_invariant_clauses`
