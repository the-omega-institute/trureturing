# All-Prime Splitting Profiles Do Not Recover Global Forms

## Abstract

A finite discriminant splitting readout at every prime does not recover a binary quadratic form, although the readout distinguishes some forms.

**Definition 1.1 (Finite discriminant splitting type).**

Lean statement: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.DiscriminantSplittingType`

*Formalization.* `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.DiscriminantSplittingType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected finite interface has three readings: inert, ramified, and split.

**Definition 1.2 (Discriminant splitting readout).**

Lean statement: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.discriminantSplittingType`

*Formalization.* `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.discriminantSplittingType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an index p, the readout maps the Jacobi symbol of the form's discriminant to inert, ramified, or split according as the value is minus one, zero, or one. It is total and decidable.

**Definition 1.3 (Equality of all-prime splitting profiles).**

Lean statement: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.SameAllPrimeSplittingProfile`

*Formalization.* `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.SameAllPrimeSplittingProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two forms have the same profile when their finite readouts agree at every natural index carrying a proof of primality.

**Theorem 1.4 (The all-prime splitting profile is not injective).**

$$\operatorname{Neq}\left(collisionFormOne, collisionFormTwo\right) \land\\\forall p: Nat, \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{discriminantSplittingType}\left(collisionFormOne, p\right) = \operatorname{discriminantSplittingType}\left(collisionFormTwo, p\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.all_prime_splitting_profile_not_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forms x squared plus y squared and x squared plus two x y plus two y squared are unequal coefficient triples, but both have discriminant minus four.

Equal discriminants give equal Jacobi readouts at every natural index, so in particular the two forms agree at every prime. Primality is only the interface label in this collision.

This deliberately proves only that the finite splitting interface is too coarse. It makes no claim of local equivalence over any ring of p-adic integers and uses no genus theory.

**Theorem 1.5 (The splitting profile distinguishes some global forms).**

$$\operatorname{Neq}\left(splitControlForm, zeroForm\right) \land\\\exists p: Nat, \operatorname{Prime}\left(p\right) \land \operatorname{Neq}\left(\operatorname{discriminantSplittingType}\left(splitControlForm, p\right), \operatorname{discriminantSplittingType}\left(zeroForm, p\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.splitting_profile_distinguishes_some_global_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The discriminant-one control form and the zero form are unequal and have different readings at the prime three. Thus the selected interface is coarse but not constant.

**Theorem 1.6 (One reference form realizes all three readings).**

$$\operatorname{discriminantSplittingType}\left(collisionFormOne, 3\right) = inert \land\\\operatorname{discriminantSplittingType}\left(collisionFormOne, 2\right) = ramified \land\\\operatorname{discriminantSplittingType}\left(collisionFormOne, 5\right) = split.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.reference_form_realizes_all_splitting_types` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero form x squared plus y squared is inert at three, ramified at two, and split at five under the selected discriminant readout.

**Theorem 1.7 (The zero form ramifies above index one).**

$$\forall p: Nat, 1 < p \Rightarrow \operatorname{discriminantSplittingType}\left(zeroForm, p\right) = ramified.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.zero_form_is_ramified_above_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero form has discriminant zero. At every index p strictly above one, the Jacobi symbol of zero is zero, so the finite readout is ramified. This weakens primality to the exact condition used.

**Theorem 1.8 (The lower index bound is necessary for zero-form ramification).**

$$\operatorname{discriminantSplittingType}\left(zeroForm, 0\right) = split \land\\\operatorname{discriminantSplittingType}\left(zeroForm, 1\right) = split.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.index_above_one_is_necessary_for_zero_form_ramification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the totalized nonprime indices zero and one, the zero form reads split rather than ramified. These concrete cases witness that the strict lower bound in the preceding theorem cannot be dropped.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.DiscriminantSplittingType`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.SameAllPrimeSplittingProfile`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.all_prime_splitting_profile_not_injective`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.discriminantSplittingType`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.index_above_one_is_necessary_for_zero_form_ramification`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.reference_form_realizes_all_splitting_types`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.splitting_profile_distinguishes_some_global_forms`
- Truth anchor: `D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.zero_form_is_ramified_above_one`
- Dependency: [D5/S3/PrimeForms/Splitting/EqualDiscriminantSplittingPortrait](EqualDiscriminantSplittingPortrait.md)
