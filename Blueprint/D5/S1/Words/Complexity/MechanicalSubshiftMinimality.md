# Minimality of Irrational Lower Mechanical Word Subshifts

## Abstract

Uniform recurrence makes every member of an irrational lower mechanical word subshift share its factor language, hence every forward orbit is dense and no proper nonempty closed shift-invariant subsystem exists.

Fix an irrational slope alpha in the half-open interval from zero to one and an arbitrary real intercept rho. Write X_alpha,rho for the prefix-language subshift of the associated lower mechanical word and F_alpha,rho(n) for its set of length-n factors.

**Theorem 1.1 (Every base factor occurs in every subshift member).**

$$y\in X_{\alpha, \rho} \Rightarrow F_{\alpha, \rho}(n) \subseteq F_{y}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordFactorSet_subset_of_mem_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a uniform recurrence bound for the prescribed mechanical factor, then realize a base-word window of that length as the prefix of y. The factor returns wholly inside this window, and translating its start gives an occurrence in y.

**Theorem 1.2 (Every subshift member has the base mechanical language).**

$$y\in X_{\alpha, \rho} \Rightarrow F_{y}(n) = F_{\alpha, \rho}(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordFactorSet_eq_of_mem_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The general subshift inclusion rules out new factors in y, while uniform recurrence supplies the reverse inclusion. The two inclusions give equality at every finite length.

**Theorem 1.3 (Every member generates the same mechanical subshift).**

$$y\in X_{\alpha, \rho} \Rightarrow X_{y} = X_{\alpha, \rho}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.wordSubshift_eq_of_mem_mechanical_wordSubshift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A prefix-language subshift is determined length by length by its factor sets, so equality of all finite languages gives equality of the generated subshifts.

**Theorem 1.4 (Every forward orbit is dense in the mechanical subshift).**

$$y\in X_{\alpha, \rho} \Rightarrow \operatorname{cl}(\operatorname{Orb}^{+}(y)) = X_{\alpha, \rho}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordSubshift_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closure of a word's forward shift orbit is its prefix-language subshift. Since every member generates X_alpha,rho, its orbit closure is exactly X_alpha,rho.

**Theorem 1.5 (There is no proper nonempty closed invariant subsystem).**

$$S \subseteq X_{\alpha, \rho} \land S \neq \emptyset \land \operatorname{Closed}(S) \land \sigma(S) \subseteq S \Rightarrow S = X_{\alpha, \rho}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordSubshift_eq_of_isClosed_shift_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a member y of the subsystem. Shift invariance contains its whole forward orbit, closedness contains the orbit closure, and minimality makes that closure all of X_alpha,rho. The assumed reverse inclusion then gives equality. No intercept-independence statement or AddAction.IsMinimal registration is asserted here.

## References

- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordFactorSet_eq_of_mem_wordSubshift`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordFactorSet_subset_of_mem_wordSubshift`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordSubshift_eq_of_isClosed_shift_invariant`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.mechanical_wordSubshift_minimal`
- Truth anchor: `D5/S1/Words/Complexity/MechanicalSubshiftMinimality.wordSubshift_eq_of_mem_mechanical_wordSubshift`
- Dependency: [D5/S1/Words/Complexity/GoldenSubshiftMinimality](GoldenSubshiftMinimality.md)
- Dependency: [D5/S1/Words/Mechanical/MechanicalUniformRecurrence](../Mechanical/MechanicalUniformRecurrence.md)
