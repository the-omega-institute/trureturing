# Reset codebook: Indexed

## Abstract

Reset codebooks, actual sources and weighted lower-memory graphs.

**Definition 1.1 (pastRec).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.pastRec`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookIndexed.pastRec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by pastRec(w : ℤ→Bool) (i : ℤ) : ℕ→ℝ→ℝ := | 0,z => z | n+1,z => Statement.f (w (i-1)) (pastRec w (i-1) n z).

**Definition 1.2 (stateRec).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by stateRec(w : ℤ→Bool) (i : ℤ) := ⨆ n, pastRec w i n 0.

**Theorem 1.3 (stateRec limit).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_limit`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : Filter.Tendsto (fun n => pastRec w i n 0) Filter.atTop (nhds (stateRec w i))

**Theorem 1.4 (stateRec interval).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_interval`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : 0 ≤ stateRec w i ∧ stateRec w i ≤ h false

**Theorem 1.5 (stateRec next).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_next`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : stateRec w (i+1)=Statement.f (w i) (stateRec w i)

**Definition 1.6 (XMinus).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.XMinus`

*Formalization.* `D5/S1/Digit/Infinite/ResetCodebookIndexed.XMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mathematical data are specified by XMinus(K n : ℕ) (tau : ℝ) : Set (ℤ → Bool) := {w | Statement.cap K w ∧ ∀ i, Statement.high K w i → tau < D5.S1.Digit.Infinite.ResetCodebook.pastRec w i n 0}.

**Theorem 1.7 (aux mem XMinus).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.aux_mem_XMinus`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.aux_mem_XMinus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (tau eps : ℝ) (w : ℤ → Bool) (hcap : Statement.cap K w) (hmargin : ∀ i, Statement.high K w i → tau + eps ≤ D5.S1.Digit.Infinite.ResetCodebook.stateRec w i) (heps : 0 < eps) (hcut : h false * rho^n < eps) : w ∈ XMinus K n tau

**Theorem 1.8 (past eq pastRec).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.past_eq_pastRec`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.past_eq_pastRec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) : Statement.past w i n z = pastRec w i n z

**Theorem 1.9 (state eq stateRec).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.state_eq_stateRec`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.state_eq_stateRec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (i : ℤ) : Statement.state w i = stateRec w i

**Theorem 1.10 (lowerLanguage eq XMinus).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.lowerLanguage_eq_XMinus`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.lowerLanguage_eq_XMinus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) : Statement.lowerLanguage K n d = XMinus K n (chi^(K-1)*d)

**Theorem 1.11 (letters end false).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.letters_end_false`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.letters_end_false` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (a : Return) (as : List Return) : ∃ u : List Bool, Statement.letters (a::as) = u ++ [false]

**Theorem 1.12 (weak word local guard).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.weak_word_local_guard`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.weak_word_local_guard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (p : ℤ) (K : ℕ) (q : ℝ) (as : List Return) (hw : Statement.weak K q as (stateRec w p)) (hprev : w (p-1)=false) (hu : ∀ j : Fin (Statement.letters as).length, w (p+(j.val:ℤ))=(Statement.letters as)[j.val]) : ∀ i : ℤ, p ≤ i → i < p+((Statement.letters as).length:ℤ) → ¬Statement.high (K+1) w i ∧ (Statement.high K w i → chi^(K-1)*q ≤ stateRec w i)

**Theorem 1.13 (concatenation cap margin).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.concatenation_cap_margin`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.concatenation_cap_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every bilateral concatenation of the complete weak equal-weight codebook with the fixed reset obeys the cap. Its finite-past evaluations tend to its state, and every high departure state is at least chi^(K-1)*d plus the same positive quantity chi^(K-1)*(B(M)-D0)*g^N.

**Theorem 1.14 (reset complete family membership).**

Lean statement: `D5/S1/Digit/Infinite/ResetCodebookIndexed.reset_complete_family_membership`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/ResetCodebookIndexed.reset_complete_family_membership` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hb : lambda-g^2*chi^K*h false < b) (hd : d = (lambda-b)/(g^2*chi^K)) (hreset : max (X false) (Y false) < Statement.B M) : 0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM ∧ ∃ n : ℕ, K ≤ n ∧ h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N ∧ ∀ w, Statement.concatenation anchor K M N d hM w → w ∈ Statement.lowerLanguage K n d

## References

- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.XMinus`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.aux_mem_XMinus`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.concatenation_cap_margin`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.letters_end_false`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.lowerLanguage_eq_XMinus`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.pastRec`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.past_eq_pastRec`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.reset_complete_family_membership`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_interval`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_limit`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.stateRec_next`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.state_eq_stateRec`
- Truth anchor: `D5/S1/Digit/Infinite/ResetCodebookIndexed.weak_word_local_guard`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookFinite](ResetCodebookFinite.md)
