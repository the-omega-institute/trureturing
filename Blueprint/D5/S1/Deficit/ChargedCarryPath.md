# Charged Raw Carry Paths

## Abstract

Raw Zeckendorf carry paths have a path-independent signed charge with exact golden-phase behavior.

**Theorem 1.1 (Each charged carry satisfies the GoldenInt ledger).**

$$\forall r, s \in \operatorname{RawDigits}, z \in \mathbb{Z},\quad \operatorname{ChargedCarryStep}\left(r, s, z\right) \Rightarrow \operatorname{betaDigits}\left(r\right) - \operatorname{betaDigits}\left(s\right) = \operatorname{intToGolden}\left(z\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.betaDigits_sub_chargedCarryStep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every labeled local carry from r to s with charge z, the expansion-face GoldenInt value of r minus that of s is intToGolden(z), the canonical integer embedding into GoldenInt. The proof checks all four constructors against phi squared equals phi plus one; the two exceptional bottom rules contribute plus one and minus one, while both internal rule families contribute zero.

**Theorem 1.2 (The one-step charge ledger telescopes along every path).**

$$\forall r, s \in \operatorname{RawDigits}, z \in \mathbb{Z},\quad \operatorname{ChargedReduces}\left(r, s, z\right) \Rightarrow \operatorname{betaDigits}\left(r\right) - \operatorname{betaDigits}\left(s\right) = \operatorname{intToGolden}\left(z\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.betaDigits_sub_chargedReduces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the charged reduction composes the constructor-level ledger. Thus the path's accumulated integer label is an independently checked semantic difference, rather than a charge defined retrospectively from its endpoints.

**Theorem 1.3 (Canonical endpoints and total charges are simultaneously unique).**

$$\forall r, s, t \in \operatorname{RawDigits}, z, w \in \mathbb{Z},\quad \operatorname{ChargedReduces}\left(r, s, z\right) \land \operatorname{CanonicalRaw}\left(s\right) \land \operatorname{ChargedReduces}\left(r, t, w\right) \land \operatorname{CanonicalRaw}\left(t\right) \Rightarrow s = t \land z = w.$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.charged_normal_form_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two charged reductions from the same raw input to canonical endpoints have equal endpoints and equal integer charges. Raw canonical uniqueness identifies each endpoint with the fixed normalizer output, while the telescoping GoldenInt ledger and injectivity of the integer coordinate identify the charges.

**Theorem 1.4 (The deterministic normalizer realizes its signed carry count).**

$$\forall r \in \operatorname{RawDigits},\quad \operatorname{ChargedReduces}\left(r, \operatorname{normalize}\left(r\right), \operatorname{carrySignedCount}\left(r\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.charged_normalize_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Following carryPass recursively produces a charged derivation to normalize(r). At every scheduler step its constructor label equals carrySign, so the accumulated path label is exactly the existing carrySignedCount recursion.

**Theorem 1.5 (The analytic deficit is the integer Beatty coboundary).**

$$\forall v_1, v_2 \in \mathbb{N},\quad \operatorname{deficit}\left(v_1, v_2\right) = \operatorname{intToReal}\left(\operatorname{beattyDeficit}\left(v_1, v_2\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.deficit_eq_beattyDeficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here intToReal is the canonical integer embedding into the reals. The public beta closed form concentrates each reading in the Zeckendorf displacement plus a linear golden-conjugate term. The linear terms cancel under addition, and the public displacement theorem converts the remaining integer expression to the golden Beatty shift coboundary.

**Theorem 1.6 (The canonical-addend carry charge equals the Beatty deficit).**

$$\forall v_1, v_2 \in \mathbb{N},\quad \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2\right)\right)\right) = \operatorname{beattyDeficit}\left(v_1, v_2\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.carrySignedCount_eq_beattyDeficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen deficit integer theorem identifies the analytic deficit with the scheduler's signed carry count. Combining it with the public deficit-Beatty identity and injectivity of the real integer cast gives an exact integer equality.

**Theorem 1.7 (Golden phase thresholds classify the signed carry charge exactly).**

$$\forall v_1, v_2 \in \mathbb{N},\quad \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2\right)\right)\right) = +1 \Leftrightarrow \operatorname{goldenPhase}\left(v_1\right) + \operatorname{goldenPhase}\left(v_2\right) < \varphi^{-1},\quad \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2\right)\right)\right) = -1 \Leftrightarrow \varphi \leq \operatorname{goldenPhase}\left(v_1\right) + \operatorname{goldenPhase}\left(v_2\right),\quad \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2\right)\right)\right) = 0 \Leftrightarrow \varphi^{-1} \leq \operatorname{goldenPhase}\left(v_1\right) + \operatorname{goldenPhase}\left(v_2\right) < \varphi.$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.carrySignedCount_phase_classifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural inputs, the signed normalization charge is plus one exactly below the inverse-golden phase threshold, minus one exactly at or above the golden-ratio threshold, and zero exactly in the intervening half-open band. This transports the existing Beatty classifier to the actual raw normalization dynamics.

**Theorem 1.8 (No fixed modulus determines the signed carry charge).**

$$\forall m \in \mathbb{N}, m \geq 2 \Rightarrow\quad \exists v_1, v_2, v_1', v_2' \in \mathbb{N},\quad v_1 \equiv v_1' (\operatorname{mod} m) \land v_2 \equiv v_2' (\operatorname{mod} m),\quad \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2\right)\right)\right) \neq \operatorname{carrySignedCount}\left(\operatorname{toRaw}\left(\operatorname{Z}\left(v_1'\right)\right) + \operatorname{toRaw}\left(\operatorname{Z}\left(v_2'\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ChargedCarryPath.carryCharge_not_determined_by_fixed_modulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural modulus m at least two, there are two natural input pairs that agree coordinatewise modulo m but have different signed normalization charges. The existing density theorem supplies pairs with unequal analytic deficits, and the deficit integer theorem transfers that inequality to carrySignedCount.

## References

- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.betaDigits_sub_chargedCarryStep`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.betaDigits_sub_chargedReduces`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.carryCharge_not_determined_by_fixed_modulus`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.carrySignedCount_eq_beattyDeficit`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.carrySignedCount_phase_classifier`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.charged_normal_form_unique`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.charged_normalize_exists`
- Truth anchor: `D5/S1/Deficit/ChargedCarryPath.deficit_eq_beattyDeficit`
- Dependency: [D5/S1/Deficit/Beatty/BetaBeattyClosedForms](Beatty/BetaBeattyClosedForms.md)
- Dependency: [D5/S1/Deficit/FixedModulusNoncongruence](FixedModulusNoncongruence.md)
- Dependency: [D5/S1/Digit/CarryStepConfluence](../Digit/CarryStepConfluence.md)
