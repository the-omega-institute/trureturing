/- GID: D5/S3/Quantum/Entanglement/MResistantQuditExistence
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/MResistantQuditExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure m-resistant qudit states exist for every admissible loss parameter. -/

/-
admission_basis: open-problem-resolution (#15010; Proved)
escape_witness: flagState_large_loss_diagonal, D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero
Escape audit unfinished under issue #15589: the dependent-family registration still lacks full source reconstruction, equivalence, variation, sensitivity, and observational-dependence evidence; the delivered-head DTR reading is `DTR-Unregistered` (Observe) for `result`, and no `declared_validated` claim is made.
Direct frozen dependencies:
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity
    statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3
  D5/S3/Quantum/Entanglement/LocalObservationPartialTraceEquivalence.partialTraceFirst
    statement_id: sha256:60de08083a292a636d655dff7f5b06843146c051021ffe2d0b604db457edc565
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
    statement_id: sha256:4607242f5ca0464588fa7eea47cf23ce7ba387f9018664f7796740270945b0f5
  D5/S3/Quantum/Information/OrthogonalRecordEntropy.pointerState
    statement_id: sha256:b17f922b32be9c031b77ef20f42ce52e9ec44b4d41a625bc43a7457ef0db6753
proof_shape: IsMResistant: definition; escape_witness: none
  consumers: claim, result
  frozen dependencies: DensityState, partialTraceFirst
proof_shape: claim: definition; escape_witness: none
  consumers: result
  frozen dependencies: DensityState, partialTraceFirst
proof_shape: basis_product: bind-only; escape_witness: none
  consumers: diagonal_separable
  frozen dependencies: pointerState
proof_shape: diagonal_separable: bind-only; escape_witness: none
  consumers: diagonal_partial_trace_separable
  frozen dependencies: DensityState, pointerState
proof_shape: partial_trace_diag: bind-only; escape_witness: none
  consumers: diagonal_partial_trace_separable
  frozen dependencies: partialTraceFirst
proof_shape: diagonal_partial_trace_separable: bind-only; escape_witness: none
  consumers: result
  frozen dependencies: partialTraceFirst, DensityState, pointerState
proof_shape: word: definition; escape_witness: none
  consumers: word_injective, flagState_kept_entangled, flagState_word, flagState_normalized, flagState_mixed_bits_zero, flagState_star, flagState_entangled, flagState_nonneg, word_restriction_injective, flagState_large_loss_diagonal, flagState_exchanged_diagonals, flagState, flagState_coherence_nonzero, flagState_support
  frozen dependencies: none
proof_shape: word_injective: bind-only; escape_witness: none
  consumers: flagState_normalized
  frozen dependencies: none
proof_shape: amplitude: definition; escape_witness: none
  consumers: flagState_word, flagState_normalized, flagState_star, flagState_entangled, amplitude_pos, flagState_nonneg, flagState, flagState_coherence_nonzero, amplitude_normSq, flagState_support
  frozen dependencies: none
proof_shape: flagState: definition; escape_witness: none
  consumers: flagState_kept_entangled, flagState_word, flagState_normalized, result, flagState_mixed_bits_zero, flagState_star, flagState_entangled, flagState_nonneg, flagState_large_loss_diagonal, flagState_exchanged_diagonals, flagState_coherence_nonzero, flagState_support
  frozen dependencies: none
proof_shape: flagState_word: bind-only; escape_witness: none
  consumers: flagState_entangled, flagState_coherence_nonzero
  frozen dependencies: none
proof_shape: flagState_support: bind-only; escape_witness: none
  consumers: flagState_mixed_bits_zero, flagState_large_loss_diagonal
  frozen dependencies: none
proof_shape: amplitude_normSq: bind-only; escape_witness: none
  consumers: flagState_normalized
  frozen dependencies: none
proof_shape: flagState_normalized: bind-only; escape_witness: none
  consumers: result
  frozen dependencies: none
proof_shape: word_restriction_injective: bind-only; escape_witness: none
  consumers: flagState_large_loss_diagonal
  frozen dependencies: none
proof_shape: family_meets_large_loss: bind-only; escape_witness: none
  consumers: flagState_large_loss_diagonal
  frozen dependencies: none
proof_shape: flagState_large_loss_diagonal: content; escape_witness: flagState_large_loss_diagonal
  consumers: result
  frozen dependencies: partialTraceFirst
proof_shape: amplitude_pos: bind-only; escape_witness: none
  consumers: flagState_entangled, flagState_coherence_nonzero
  frozen dependencies: none
proof_shape: flagState_nonneg: bind-only; escape_witness: none
  consumers: flagState_coherence_nonzero
  frozen dependencies: none
proof_shape: flagState_star: bind-only; escape_witness: none
  consumers: flagState_coherence_nonzero
  frozen dependencies: none
proof_shape: flagState_coherence_nonzero: bind-only; escape_witness: none
  consumers: flagState_kept_entangled
  frozen dependencies: partialTraceFirst
proof_shape: flagState_mixed_bits_zero: bind-only; escape_witness: none
  consumers: flagState_entangled, flagState_exchanged_diagonals
  frozen dependencies: none
proof_shape: flagState_exchanged_diagonals: bind-only; escape_witness: none
  consumers: flagState_kept_entangled
  frozen dependencies: partialTraceFirst
proof_shape: flagState_kept_entangled: content; escape_witness: D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero
  consumers: result
  frozen dependencies: DensityState, partialTraceFirst
proof_shape: flagState_entangled: content; escape_witness: D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction.separable_exchange_zero
  consumers: result
  frozen dependencies: DensityState
proof_shape: result: content; escape_witness: flagState_large_loss_diagonal
  consumers: none (settling result)
  frozen dependencies: DensityState, partialTraceFirst, pointerState
Definitions are not proof declarations. Compiler-generated proof constants inherit
the identity of their frozen source owner; they have no separate Freeze identity.
utility none: arbitrary finite carriers and universal constructions; no bounded
enumeration, checker, numeric reduction, or certified finite instance.
-/

import D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import D5.S3.Quantum.PureState.PureStateHandshake

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Entanglement.MResistantQuditExistence
open D5.S3.Quantum.Entanglement.FullySeparableExchangeObstruction
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

variable {V L : Type} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

def IsMResistant {V L : Type} [Fintype V] [DecidableEq V]
    [Fintype L] [DecidableEq L] (m : ℕ) (ψ : (V → L) → ℂ) : Prop :=
  (¬ IsFullySeparableLocal (rankOneDensity ψ)) ∧
  (∀ J : Finset V, J.card = m →
    ¬ IsFullySeparableLocal (partialTraceLocal (rankOneDensity ψ) J)) ∧
  (∀ J : Finset V, J.card = m + 1 →
    IsFullySeparableLocal (partialTraceLocal (rankOneDensity ψ) J))

def claim : Prop := ∀ N m : ℕ, 3 ≤ N → m + 2 ≤ N →
  ∃ (d : ℕ) (ψ : (Fin N → Fin d) → ℂ),
    (∑ x, Complex.normSq (ψ x)) = 1 ∧ IsMResistant m ψ

open D5.S3.Quantum.Information.OrthogonalRecordEntropy (pointerState)

omit [DecidableEq V] in
private theorem basis_product (q x y : V → L) :
    (∏ v, (pointerState (q v)).val (x v) (y v)) =
      if x = q ∧ y = q then 1 else 0 := by
  classical
  by_cases hx : x = q
  · subst x
    by_cases hy : y = q
    · subst y
      simp [pointerState]
    · obtain ⟨v, hv⟩ := Function.ne_iff.mp hy
      have he : (pointerState (q v)).val (q v) (y v) = 0 := by
        simp [pointerState, Ne.symm hv]
      rw [Finset.prod_eq_zero (Finset.mem_univ v) he]
      simp [hy]
  · obtain ⟨v, hv⟩ := Function.ne_iff.mp hx
    have he : (pointerState (q v)).val (x v) (y v) = 0 := by
      by_cases hxy : x v = y v
      · have hyq : y v ≠ q v := fun h => hv (hxy.trans h)
        simp [pointerState, hxy, hyq]
      · simp [pointerState, hxy]
    rw [Finset.prod_eq_zero (Finset.mem_univ v) he]
    simp [hx]

/-- A probability distribution on product-basis configurations is fully separable. -/
private theorem diagonal_separable (ρ : Matrix (V → L) (V → L) ℂ) (w : (V → L) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (he : ∀ x y, ρ x y = if x = y then (w x : ℂ) else 0) :
    IsFullySeparableLocal ρ := by
  classical
  let e := Fintype.equivFin (V → L)
  refine ⟨Fintype.card (V → L), w ∘ e.symm,
    fun j v => pointerState (e.symm j v), fun j => hw _, ?_, ?_⟩
  · exact (e.symm.sum_comp w).trans hs
  · intro x y
    rw [he]
    change _ = ∑ j, (w (e.symm j) : ℂ) * ∏ v, (pointerState (e.symm j v)).val (x v) (y v)
    rw [e.symm.sum_comp (fun q => (w q : ℂ) * ∏ v, (pointerState (q v)).val (x v) (y v))]
    simp_rw [basis_product]
    by_cases hxy : x = y
    · subst y
      simp
    · have hfalse (q : V → L) : ¬ (x = q ∧ y = q) := by
        rintro ⟨hx, hy⟩
        exact hxy (hx.trans hy.symm)
      simp [hxy, hfalse]


private theorem partial_trace_diag (ψ : (V → L) → ℂ) (J : Finset V)
    (x : {v : V // v ∉ J} → L) :
    partialTraceLocal (rankOneDensity ψ) J x x =
      ((∑ z : J → L, Complex.normSq (ψ (joinLocal J z x)) : ℝ) : ℂ) := by
  change (∑ z : J → L, ψ (joinLocal J z x) * star (ψ (joinLocal J z x))) = _
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact Complex.mul_conj _

/-- A normalized pure state's diagonal marginal is a probability distribution. -/
private theorem diagonal_partial_trace_separable (ψ : (V → L) → ℂ)
    (hψ : ∑ x, Complex.normSq (ψ x) = 1) (J : Finset V)
    (hdiag : ∀ x y, x ≠ y → partialTraceLocal (rankOneDensity ψ) J x y = 0) :
    IsFullySeparableLocal (partialTraceLocal (rankOneDensity ψ) J) := by
  classical
  let w := fun x : {v : V // v ∉ J} → L => ∑ z : J → L, Complex.normSq (ψ (joinLocal J z x))
  apply diagonal_separable _ w
  · intro x
    exact Finset.sum_nonneg (fun z _ => Complex.normSq_nonneg _)
  · change (∑ x, ∑ z : J → L, Complex.normSq (ψ (joinLocal J z x))) = 1
    rw [Finset.sum_comm]
    have he := (Equiv.piEquivPiSubtypeProd (fun v => v ∈ J) (fun _ => L)).symm.sum_comp (fun x => Complex.normSq (ψ x))
    rw [Fintype.sum_prod_type] at he
    exact he.trans hψ
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, eq_self]
      exact partial_trace_diag ψ J x
    · simp only [if_neg hxy]
      exact hdiag x y hxy



private def word (e : (Finset V × Bool) ≃ L) (k : ℕ) (t : ({S : Finset V // S.card = k} × Bool)) (i : V) : L :=
  e (t.1.val, if i ∈ t.1.val then t.2 else false)

omit [Fintype V] [Fintype L] [DecidableEq L] in
private theorem word_injective (e : (Finset V × Bool) ≃ L) (k : ℕ) (hk : 1 ≤ k) :
    Function.Injective (word e k) := by
  intro t t' h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < t.1.val.card by rw [t.1.property]; omega)
  have he := e.injective (congrFun h i)
  change (t.1.val, if i ∈ t.1.val then t.2 else false) =
    (t'.1.val, if i ∈ t'.1.val then t'.2 else false) at he
  have hS : t.1 = t'.1 := Subtype.ext (congrArg Prod.fst he)
  have hi' : i ∈ t'.1.val := by rwa [← hS]
  apply Prod.ext hS
  simpa [hi, hi'] using congrArg Prod.snd he

private def amplitude (T : Type) [Fintype T] : ℝ := (Real.sqrt (Fintype.card T : ℝ))⁻¹

private def flagState (e : (Finset V × Bool) ≃ L) (k : ℕ) (x : V → L) : ℂ :=
  if x ∈ Finset.univ.image (word e k) then (amplitude (({S : Finset V // S.card = k} × Bool)) : ℂ) else 0

omit [Fintype L] in
private theorem flagState_word (e : (Finset V × Bool) ≃ L) (k : ℕ) (t : ({S : Finset V // S.card = k} × Bool)) :
    flagState e k (word e k t) = (amplitude (({S : Finset V // S.card = k} × Bool)) : ℂ) := by
  classical
  simp [flagState]

omit [Fintype L] in
private theorem flagState_support (e : (Finset V × Bool) ≃ L) (k : ℕ) (x : V → L)
    (h : flagState e k x ≠ 0) : ∃ t : ({S : Finset V // S.card = k} × Bool), word e k t = x := by
  classical
  by_cases hx : x ∈ Finset.univ.image (word e k)
  · simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hx
  · simp [flagState, hx] at h

private theorem amplitude_normSq {T : Type} [Fintype T] (hT : 0 < Fintype.card T) :
    Complex.normSq (amplitude T : ℂ) = (Fintype.card T : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hs : (Real.sqrt (Fintype.card T : ℝ)) ^ 2 = (Fintype.card T : ℝ) :=
    Real.sq_sqrt hn.le
  rw [amplitude, Complex.normSq_ofReal, ← pow_two, inv_pow, hs]

/-- The uniform superposition of the distinct flag-coded product vectors is normalized. -/
private theorem flagState_normalized (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ x, Complex.normSq (flagState e k x) = 1 := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset V).card by simpa using hkn)
  letI : Nonempty (({S : Finset V // S.card = k} × Bool)) := ⟨(⟨S, hS⟩, false)⟩
  have hT : 0 < Fintype.card (({S : Finset V // S.card = k} × Bool)) := Fintype.card_pos
  let A := Finset.univ.image (word e k)
  have hinj := word_injective e k hk
  calc
    (∑ x, Complex.normSq (flagState e k x)) = ∑ x ∈ A, Complex.normSq (flagState e k x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ A)
      intro x _ hx
      simp [flagState, show x ∉ Finset.univ.image (word e k) from hx]
    _ = ∑ x ∈ A, Complex.normSq (amplitude (({S : Finset V // S.card = k} × Bool)) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [flagState, if_pos (show x ∈ Finset.univ.image (word e k) from hx)]
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, amplitude_normSq hT]
      simp only [A, Finset.card_image_of_injective _ hinj, Finset.card_univ]
      exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hT)

omit [Fintype V] [Fintype L] [DecidableEq L] in
private theorem word_restriction_injective (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (J : Finset V) (hJ : J.Nonempty)
    (hmeets : ∀ S : {S : Finset V // S.card = k}, ∃ i ∈ J, i ∈ S.val) :
    Function.Injective (fun t : ({S : Finset V // S.card = k} × Bool) => fun i : J => word e k t i.val) := by
  intro t t' h
  obtain ⟨j, hj⟩ := hJ
  have he := e.injective (congrFun h ⟨j, hj⟩)
  have hS : t.1 = t'.1 := Subtype.ext (congrArg Prod.fst he)
  obtain ⟨i, hiJ, hiS⟩ := hmeets t.1
  have he' := e.injective (congrFun h ⟨i, hiJ⟩)
  have hiS' : i ∈ t'.1.val := by rwa [← hS]
  apply Prod.ext hS
  simpa [word, hiS, hiS'] using congrArg Prod.snd he'

omit [DecidableEq V] in
private theorem family_meets_large_loss (k : ℕ) (J : Finset V)
    (hlarge : Fintype.card V < k + J.card) (S : {S : Finset V // S.card = k}) :
    ∃ i ∈ J, i ∈ S.val := by
  classical
  by_contra h
  have hsubset : S.val ⊆ Jᶜ := by
    intro i hi
    simp only [Finset.mem_compl]
    intro hiJ
    exact h ⟨i, hiJ, hi⟩
  have hc := Finset.card_le_card hsubset
  rw [S.property, Finset.card_compl] at hc
  have hJle := Finset.card_le_univ J
  omega

/-- Losing enough sites distinguishes every flag-coded summand and removes all coherence. -/
private theorem flagState_large_loss_diagonal (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (J : Finset V) (hJ : J.Nonempty) (hlarge : Fintype.card V < k + J.card)
    (x y : {v : V // v ∉ J} → L) (hxy : x ≠ y) :
    partialTraceLocal (rankOneDensity (flagState e k)) J x y = 0 := by
  classical
  change (∑ z : J → L, flagState e k (joinLocal J z x) *
    star (flagState e k (joinLocal J z y))) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_cases hx : flagState e k (joinLocal J z x) = 0
  · simp [hx]
  by_cases hy : flagState e k (joinLocal J z y) = 0
  · simp [hy]
  obtain ⟨t, ht⟩ := flagState_support e k _ hx
  obtain ⟨t', ht'⟩ := flagState_support e k _ hy
  have htt : t = t' := word_restriction_injective e k J hJ
    (family_meets_large_loss k J hlarge) (by
      funext i
      change word e k t i.val = word e k t' i.val
      rw [ht, ht']
      simp [joinLocal, i.property])
  have heq : x = y := by
    funext i
    have h := congrFun (ht.symm.trans (htt ▸ ht')) i.val
    simpa [joinLocal, i.property] using h
  exact (hxy heq).elim


private theorem amplitude_pos {T : Type} [Fintype T] [Nonempty T] : 0 < amplitude T := by
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  exact_mod_cast Fintype.card_pos (α := T)

omit [Fintype L] in
private theorem flagState_nonneg (e : (Finset V × Bool) ≃ L) (k : ℕ) (x : V → L) :
    0 ≤ flagState e k x := by
  classical
  unfold flagState
  split_ifs
  · apply Complex.zero_le_real.mpr
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · exact le_rfl

omit [Fintype L] in
private theorem flagState_star (e : (Finset V × Bool) ≃ L) (k : ℕ) (x : V → L) :
    star (flagState e k x) = flagState e k x := by
  classical
  unfold flagState
  split_ifs <;> simp

/-- The kept copies of two disjoint-edge branches retain a strictly positive coherence. -/
private theorem flagState_coherence_nonzero (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (S : {S : Finset V // S.card = k}) (J : Finset V) (hSJ : ∀ i ∈ J, i ∉ S.val) :
    partialTraceLocal (rankOneDensity (flagState e k)) J
      (fun i => word e k (S, false) i.val)
      (fun i => word e k (S, true) i.val) ≠ 0 := by
  classical
  letI : Nonempty (({S : Finset V // S.card = k} × Bool)) := ⟨(S, false)⟩
  let z : J → L := fun i => word e k (S, false) i.val
  let x : {v : V // v ∉ J} → L := fun i => word e k (S, false) i.val
  let y : {v : V // v ∉ J} → L := fun i => word e k (S, true) i.val
  have hx : joinLocal J z x = word e k (S, false) := by
    funext i
    simp [joinLocal, z, x]
  have hy : joinLocal J z y = word e k (S, true) := by
    funext i
    by_cases hi : i ∈ J
    · simp [joinLocal, z, hi, word, hSJ i hi]
    · simp [joinLocal, y, hi]
  have hn (w : J → L) : 0 ≤ flagState e k (joinLocal J w x) *
      star (flagState e k (joinLocal J w y)) := by
    rw [flagState_star]
    exact mul_nonneg (flagState_nonneg e k _) (flagState_nonneg e k _)
  have hp : 0 < flagState e k (joinLocal J z x) * star (flagState e k (joinLocal J z y)) := by
    rw [hx, hy, flagState_word, flagState_word, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    exact Complex.zero_lt_real.mpr (mul_pos amplitude_pos amplitude_pos)
  change (∑ w : J → L, flagState e k (joinLocal J w x) *
    star (flagState e k (joinLocal J w y))) ≠ 0
  exact ne_of_gt (hp.trans_le (Finset.single_le_sum (fun w _ => hn w) (Finset.mem_univ z)))

omit [Fintype L] in
/-- Opposite bits at two sites of the same flag are outside the support. -/
private theorem flagState_mixed_bits_zero (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (S : {S : Finset V // S.card = k}) (i j : V) (hi : i ∈ S.val) (hj : j ∈ S.val)
    (q : V → L) (hqi : q i = e (S.val, true)) (hqj : q j = e (S.val, false)) :
    flagState e k q = 0 := by
  classical
  by_contra hq
  obtain ⟨t, ht⟩ := flagState_support e k q hq
  have hpairi := e.injective ((congrFun ht i).trans hqi)
  have hpairj := e.injective ((congrFun ht j).trans hqj)
  have hlabel : t.1.val = S.val := congrArg Prod.fst hpairi
  have hbi : t.2 = true := by
    simpa [word, hlabel, hi] using congrArg Prod.snd hpairi
  have hbj : t.2 = false := by
    simpa [word, hlabel, hj] using congrArg Prod.snd hpairj
  exact Bool.false_ne_true (hbj.symm.trans hbi)



/-- Both diagonals created by exchanging one bit of the two kept branches vanish. -/
private theorem flagState_exchanged_diagonals (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (S : {S : Finset V // S.card = k}) (J : Finset V) (i j : {v : V // v ∉ J})
    (hi : i.val ∈ S.val) (hj : j.val ∈ S.val) (hij : i ≠ j) :
    let x : {v : V // v ∉ J} → L := fun r => word e k (S, false) r.val
    let y : {v : V // v ∉ J} → L := fun r => word e k (S, true) r.val
    partialTraceLocal (rankOneDensity (flagState e k)) J
      (Function.update x i (y i)) (Function.update x i (y i)) = 0 ∧
    partialTraceLocal (rankOneDensity (flagState e k)) J
      (Function.update y i (x i)) (Function.update y i (x i)) = 0 := by
  classical
  dsimp only
  constructor
  · change (∑ z : J → L, flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, false) r.val) i (word e k (S, true) i.val))) *
      star (flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, false) r.val) i (word e k (S, true) i.val))))) = 0
    apply Finset.sum_eq_zero
    intro z _
    have hzero : flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, false) r.val) i (word e k (S, true) i.val))) = 0 := by
      apply flagState_mixed_bits_zero e k S i.val j.val hi hj
      · simp [joinLocal, i.property, word, hi]
      · simp [joinLocal, j.property, Function.update_of_ne hij.symm, word]
    simp [hzero]
  · change (∑ z : J → L, flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, true) r.val) i (word e k (S, false) i.val))) *
      star (flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, true) r.val) i (word e k (S, false) i.val))))) = 0
    apply Finset.sum_eq_zero
    intro z _
    have hzero : flagState e k (joinLocal J z
        (Function.update (fun r => word e k (S, true) r.val) i (word e k (S, false) i.val))) = 0 := by
      apply flagState_mixed_bits_zero e k S j.val i.val hj hi
      · simp [joinLocal, j.property, Function.update_of_ne hij.symm, word, hj]
      · simp [joinLocal, i.property, word]
    simp [hzero]


/-- With k kept sites, their common flag gives an entanglement witness. -/
private theorem flagState_kept_entangled (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (hk : 2 ≤ k) (J : Finset V) (hcard : Jᶜ.card = k) :
    ¬ IsFullySeparableLocal (partialTraceLocal (rankOneDensity (flagState e k)) J) := by
  classical
  let S : {S : Finset V // S.card = k} := ⟨Jᶜ, hcard⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < S.val.card by rw [S.property]; omega)
  have hiJ : i ∉ J := Finset.mem_compl.mp hi
  have hjJ : j ∉ J := Finset.mem_compl.mp hj
  let iR : {v : V // v ∉ J} := ⟨i, hiJ⟩
  let jR : {v : V // v ∉ J} := ⟨j, hjJ⟩
  let x : {v : V // v ∉ J} → L := fun r => word e k (S, false) r.val
  let y : {v : V // v ∉ J} → L := fun r => word e k (S, true) r.val
  let u := Function.update x iR (y iR)
  have hijR : iR ≠ jR := fun h => hij (congrArg Subtype.val h)
  have hzero : partialTraceLocal (rankOneDensity (flagState e k)) J u u = 0 :=
    (flagState_exchanged_diagonals e k S J iR jR hi hj hijR).1
  have hc : partialTraceLocal (rankOneDensity (flagState e k)) J x y ≠ 0 :=
    flagState_coherence_nonzero e k S J (by
      intro a ha
      change a ∉ Jᶜ
      simpa using ha)
  intro hsep
  exact hc (separable_exchange_zero _ hsep x y iR hzero)

/-- The pure flag-coded state is itself entangled. -/
private theorem flagState_entangled (e : (Finset V × Bool) ≃ L) (k : ℕ)
    (hk : 2 ≤ k) (hkn : k ≤ Fintype.card V) :
    ¬ IsFullySeparableLocal (rankOneDensity (flagState e k)) := by
  classical
  obtain ⟨A, _, hA⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset V).card by simpa using hkn)
  let S : {S : Finset V // S.card = k} := ⟨A, hA⟩
  letI : Nonempty (({S : Finset V // S.card = k} × Bool)) := ⟨(S, false)⟩
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
    (show 1 < S.val.card by rw [S.property]; omega)
  let x := word e k (S, false)
  let y := word e k (S, true)
  let u := Function.update x i (y i)
  have hu : flagState e k u = 0 := by
    apply flagState_mixed_bits_zero e k S i j hi hj
    · simp [u, y, word, hi]
    · rw [show u j = x j from Function.update_of_ne hij.symm _ _]
      simp [x, word]
  have hc : rankOneDensity (flagState e k) x y ≠ 0 := by
    change flagState e k x * star (flagState e k y) ≠ 0
    rw [flagState_word, flagState_word, Complex.star_def, Complex.conj_ofReal]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt amplitude_pos))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt amplitude_pos))
  intro hsep
  exact hc (separable_exchange_zero _ hsep x y i (by
    change flagState e k u * star (flagState e k u) = 0
    rw [hu]
    simp))


/-- Every admissible particle number and resistance parameter has a normalized pure qudit state. -/
theorem result : claim := by
  classical
  intro N m hN hm
  let k := N - m
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkn : k ≤ Fintype.card (Fin N) := by simp [k]
  let e : (Finset (Fin N) × Bool) ≃ Fin (Fintype.card (Finset (Fin N) × Bool)) :=
    Fintype.equivFin _
  have hnorm := flagState_normalized e k (by omega) hkn
  refine ⟨Fintype.card (Finset (Fin N) × Bool), flagState e k, hnorm, ?_⟩
  refine ⟨flagState_entangled e k hk hkn, ?_, ?_⟩
  · intro J hJ
    apply flagState_kept_entangled e k hk J
    simp only [Finset.card_compl, Fintype.card_fin, hJ]
    rfl
  · intro J hJ
    apply diagonal_partial_trace_separable (flagState e k) hnorm J
    intro x y hxy
    apply flagState_large_loss_diagonal e k J _ _ x y hxy
    · apply Finset.card_pos.mp
      rw [hJ]
      omega
    · simp only [Fintype.card_fin, hJ]
      dsimp [k]
      omega


end D5.S3.Quantum.Entanglement.MResistantQuditExistence
