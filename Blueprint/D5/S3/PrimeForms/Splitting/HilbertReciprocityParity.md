# Hilbert Reciprocity as a Global Sign-Parity Check

## Abstract

A finite sign code recovers one coordinate and exposes omitted load-bearing places.

**Definition 1.1 (Hilbert reciprocity code).**

Lean statement: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.hilbertReciprocityCode`

*Formalization.* `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.hilbertReciprocityCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A codeword is a sign profile with a finite carrier, value one away from that carrier, and product one on the carrier.

Hilbert symbols form one arithmetic instance of this abstraction. This module does not define or construct a Hilbert symbol.

**Theorem 1.2 (One local sign is determined by all the others).**

$$\begin{aligned}\forall I, S: \operatorname{Finset}\left(I\right), s: I \to ZUnits, v0: I, [\operatorname{DecidableEq}\left(I\right)],\\(\forall v, \neg(v \in S) \Rightarrow s(v) = 1) \land \\\prod_{v \in S} s(v) = 1 \Rightarrow \\s(v0) = \prod_{v \in \operatorname{erase}\left(S, v0\right)} s(v).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.local_sign_eq_product_of_other_places` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product-one equation is the explicit hReciprocity premise. For actual Hilbert symbols it comes from the external classical product formula and is not proved or anchored here.

Factoring out the chosen coordinate and using that every integer unit is its own inverse gives the product over the remaining finite carrier. A coordinate outside the carrier is one.

**Theorem 1.3 (Omitting a load-bearing place can break the check).**

$$\begin{aligned}\forall v: Fin2, s(v) = -1,\\\operatorname{InCode}\left(s\right) \land \prod_{v \in \operatorname{univ}\left(Fin2\right)} s(v) = 1 \land \\\forall w: Fin2, \prod_{v \in \operatorname{erase}\left(\operatorname{univ}\left(Fin2\right), w\right)} s(v) = -1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.omitted_place_can_break_reciprocity_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On two coordinates, assigning minus one at both gives total product one. Deleting either coordinate leaves product minus one. The abstract coordinates model omitted dyadic or infinite places without constructing arithmetic Hilbert symbols.

**Theorem 1.4 (Degenerate carriers and profiles are explicit).**

$$\begin{aligned}\operatorname{InCode}\left(emptyProfile\right) \land \\\forall s: \operatorname{Profile}\left(Unit\right), \operatorname{InCode}\left(s\right) \Rightarrow s(unit) = 1 \land \\\forall I, \operatorname{InCode}\left(\operatorname{allOneProfile}\left(I\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.reciprocity_code_degeneracy_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty profile and every all-one profile pass. On a singleton index type, every codeword is forced to have its sole coordinate equal to one.

**Theorem 1.5 (The reciprocity product premise is necessary).**

$$\begin{aligned}\forall v: Fin1, s(v) = -1,\\\prod_{v \in \operatorname{univ}\left(Fin1\right)} s(v) \neq 1 \land \\s(0) \neq \prod_{v \in \operatorname{erase}\left(\operatorname{univ}\left(Fin1\right), 0\right)} s(v).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.reciprocity_product_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-coordinate profile with value minus one has finite support but fails both the product-one premise and local recovery.

**Theorem 1.6 (The finite carrier must cover every nontrivial sign).**

$$\begin{aligned}s(0) = 1, s(1) = -1,\\\prod_{v \in \operatorname{singleton}\left(0\right)} s(v) = 1 \land \\\neg(\forall v, \neg(v \in \operatorname{singleton}\left(0\right)) \Rightarrow s(v) = 1) \land \\s(1) \neq \prod_{v \in \operatorname{erase}\left(\operatorname{singleton}\left(0\right), 1\right)} s(v).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.finite_support_coverage_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A claimed carrier containing only a positive coordinate has product one, but a negative coordinate outside it violates local recovery. Thus the off-carrier identity condition is necessary.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.finite_support_coverage_is_necessary`
- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.hilbertReciprocityCode`
- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.local_sign_eq_product_of_other_places`
- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.omitted_place_can_break_reciprocity_check`
- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.reciprocity_code_degeneracy_audit`
- Truth anchor: `D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.reciprocity_product_is_necessary`
