/- GID: D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Algebra.TrivSqZeroExt.Ideal]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.claim; result=D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.result; claim=D5/S0/Certificates/Algebra/ChakrabortyPatraIdealZeroProductRefutation.claim
   digest: A binary square-zero extension refutes Chakraborty-Patra Conjecture 4.2. -/

import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.IsField
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The ideal zero-product probability of a binary square-zero extension. -/

set_option autoImplicit false

namespace D5.S0.Certificates.Algebra.ChakrabortyPatraIdealZeroProductRefutation

open scoped BigOperators
open TrivSqZeroExt

/-- The fraction of ordered tuples of ideals whose ideal product is zero. -/
noncomputable def zeta (S : Type) [CommRing S] (k : ℕ) : ℚ :=
  (Nat.card {I : Fin k → Ideal S // (∏ i, I i) = ⊥} : ℚ) /
    (Nat.card (Ideal S) : ℚ) ^ k

/-- Chakraborty–Patra, Conjecture 4.2 in arXiv:2608.14618v1. -/
def claim : Prop :=
  ∀ (S : Type) [CommRing S] [Finite S] (k : ℕ),
    2 ≤ k → zeta S k = 1 - (1 : ℚ) / (2 : ℚ) ^ k → IsField S

private abbrev K := ZMod 2
private abbrev V := K × K
private abbrev R := TrivSqZeroExt K V

private abbrev radical : Ideal R := kerIdeal K V
private abbrev emb : V → R := inr
private abbrev a : V := (1, 0)
private abbrev b : V := (0, 1)
private abbrev c : V := (1, 1)

private theorem ring_card : Nat.card R = 8 := by
  change Nat.card (K × (K × K)) = 8
  simp [Nat.card_eq_fintype_card, ZMod.card]

private theorem scalar_cases (t : K) : t = 0 ∨ t = 1 := by
  change Fin 2 at t
  change t = (0 : Fin 2) ∨ t = 1
  fin_cases t <;> decide

private theorem vector_cases (v : V) : v = 0 ∨ v = a ∨ v = b ∨ v = c := by
  obtain ⟨x, y⟩ := v
  rcases scalar_cases x with rfl | rfl <;>
    rcases scalar_cases y with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inr rfl))

@[simp] private theorem emb_mem_radical (v : V) : emb v ∈ radical :=
  (mem_kerIdeal_iff_inr K V _).mpr (by rw [snd_inr])

private theorem one_not_mem_radical : (1 : R) ∉ radical := by
  intro h
  have h' := congrArg TrivSqZeroExt.fst ((mem_kerIdeal_iff_inr K V _).mp h)
  exact one_ne_zero (by simpa only [fst_one, fst_inr] using h')

private theorem radical_proper : radical ≠ ⊤ := by
  intro h
  have h1 : (1 : R) ∈ (⊤ : Ideal R) := by simp
  rw [← h] at h1
  exact one_not_mem_radical h1

private theorem proper_le_radical (I : Ideal R) (hI : I ≠ ⊤) : I ≤ radical := by
  intro x hx
  have hx0 : x.fst = 0 := by
    by_contra h
    have h1 : x.fst = 1 := (scalar_cases x.fst).resolve_left h
    have hu : IsUnit x.fst := h1.symm ▸ isUnit_one
    exact hI (I.eq_top_of_isUnit_mem hx (isUnit_iff_isUnit_fst.mpr hu))
  exact (mem_kerIdeal_iff_inr K V x).mpr (by
    rw [← x.inl_fst_add_inr_snd_eq, hx0, inl_zero, zero_add]
    simp)

private abbrev line (v : V) : Ideal R := Ideal.span {emb v}

private theorem line_le_radical (v : V) : line v ≤ radical :=
  (Ideal.span_singleton_le_iff_mem (I := radical)).mpr (emb_mem_radical v)

private theorem emb_mul (x : R) (v : V) : x * emb v = emb (x.fst • v) := by
  calc
    x * emb v = (inl x.fst + inr x.snd) * emb v := by rw [x.inl_fst_add_inr_snd_eq]
    _ = emb (x.fst • v) := by rw [add_mul, inl_mul_inr, inr_mul_inr, add_zero]

private theorem mem_line (v : V) (x : R) : x ∈ line v ↔ x = 0 ∨ x = emb v := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h
    rw [emb_mul] at ht
    rcases scalar_cases t.fst with h0 | h1
    · left
      simpa only [h0, zero_smul, inr_zero] using ht.symm
    · right
      simpa only [h1, one_smul] using ht.symm
  · rintro (rfl | rfl)
    · exact (line v).zero_mem
    · exact Ideal.mem_span_singleton_self _

@[simp] private theorem emb_eq_zero (v : V) : emb v = 0 ↔ v = 0 := by
  rw [← inr_zero (R := K) (M := V)]
  exact (inr_injective (R := K)).eq_iff

@[simp] private theorem emb_mem_line (u v : V) : emb u ∈ line v ↔ u = 0 ∨ u = v := by
  rw [mem_line, emb_eq_zero, (inr_injective (R := K)).eq_iff]

@[simp] private theorem emb_mem_bot (u : V) : emb u ∈ (⊥ : Ideal R) ↔ u = 0 := by
  rw [Ideal.mem_bot, emb_eq_zero]

private theorem proper_ext {I J : Ideal R} (hI : I ≤ radical) (hJ : J ≤ radical)
    (ha : emb a ∈ I ↔ emb a ∈ J) (hb : emb b ∈ I ↔ emb b ∈ J)
    (hc : emb c ∈ I ↔ emb c ∈ J) : I = J := by
  have transfer (A B : Ideal R) (hA : A ≤ radical)
      (ha' : emb a ∈ A → emb a ∈ B) (hb' : emb b ∈ A → emb b ∈ B)
      (hc' : emb c ∈ A → emb c ∈ B) : A ≤ B := by
    intro x hx
    have h := (mem_kerIdeal_iff_inr K V x).mp (hA hx)
    rw [h] at hx ⊢
    rcases vector_cases x.snd with h0 | h1 | h2 | h3
    · rw [h0, inr_zero]
      exact B.zero_mem
    · rw [h1] at hx ⊢
      exact ha' hx
    · rw [h2] at hx ⊢
      exact hb' hx
    · rw [h3] at hx ⊢
      exact hc' hx
  exact le_antisymm (transfer I J hI ha.mp hb.mp hc.mp)
    (transfer J I hJ ha.mpr hb.mpr hc.mpr)

private theorem add_ab : a + b = c := by decide
private theorem add_ac : a + c = b := by decide
private theorem add_bc : b + c = a := by decide

private theorem not_a0 : a ≠ 0 := by decide
private theorem not_b0 : b ≠ 0 := by decide
private theorem not_c0 : c ≠ 0 := by decide
private theorem not_ab : a ≠ b := by decide
private theorem not_ac : a ≠ c := by decide
private theorem not_bc : b ≠ c := by decide

attribute [local simp] not_a0 not_b0 not_c0 not_ab not_ac not_bc

private theorem not_ba : b ≠ a := Ne.symm not_ab
private theorem not_ca : c ≠ a := Ne.symm not_ac
private theorem not_cb : c ≠ b := Ne.symm not_bc

attribute [local simp] not_ba not_ca not_cb

private def idealAt : Fin 6 → Ideal R := ![⊥, line a, line b, line c, radical, ⊤]

private theorem ideal_at_surjective : Function.Surjective idealAt := by
  intro I
  classical
  by_cases htop : I = ⊤
  · exact ⟨5, htop.symm⟩
  have hI := proper_le_radical I htop
  have add_mem {u v : V} (hu : emb u ∈ I) (hv : emb v ∈ I) : emb (u + v) ∈ I := by
    change inr (u + v) ∈ I
    rw [inr_add]
    exact I.add_mem hu hv
  by_cases ha : emb a ∈ I
  · by_cases hb : emb b ∈ I
    · have hc := add_mem ha hb
      rw [add_ab] at hc
      refine ⟨4, (proper_ext hI le_rfl ?_ ?_ ?_).symm⟩ <;> simp [ha, hb, hc]
    · have hc : emb c ∉ I := fun hc => hb (add_ac ▸ add_mem ha hc)
      refine ⟨1, (proper_ext hI (line_le_radical a) ?_ ?_ ?_).symm⟩ <;> simp [ha, hb, hc]
  · by_cases hb : emb b ∈ I
    · have hc : emb c ∉ I := fun hc => ha (add_bc ▸ add_mem hb hc)
      refine ⟨2, (proper_ext hI (line_le_radical b) ?_ ?_ ?_).symm⟩ <;> simp [ha, hb, hc]
    · by_cases hc : emb c ∈ I
      · refine ⟨3, (proper_ext hI (line_le_radical c) ?_ ?_ ?_).symm⟩ <;> simp [ha, hb, hc]
      · refine ⟨0, (proper_ext hI bot_le ?_ ?_ ?_).symm⟩ <;> simp [ha, hb, hc]

private theorem ideal_at_le_radical (i : Fin 6) (hi : i ≠ 5) : idealAt i ≤ radical := by
  fin_cases i
  · exact bot_le
  · exact line_le_radical a
  · exact line_le_radical b
  · exact line_le_radical c
  · exact le_rfl
  · exact (hi rfl).elim

private theorem top_ne_ideal_at {i : Fin 6} (hi : i ≠ 5) : (⊤ : Ideal R) ≠ idealAt i := by
  intro h
  exact radical_proper (top_le_iff.mp (h ▸ ideal_at_le_radical i hi))

private theorem ideal_at_injective : Function.Injective idealAt := by
  intro i j h
  have ha := SetLike.ext_iff.mp h (emb a)
  have hb := SetLike.ext_iff.mp h (emb b)
  have hc := SetLike.ext_iff.mp h (emb c)
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exfalso
      exact top_ne_ideal_at (by decide) h
    | exfalso
      exact top_ne_ideal_at (by decide) h.symm
    | simp [idealAt] at ha hb hc

private noncomputable def idealEquiv : Fin 6 ≃ Ideal R :=
  Equiv.ofBijective idealAt ⟨ideal_at_injective, ideal_at_surjective⟩

private theorem ideal_card : Nat.card (Ideal R) = 6 :=
  Nat.card_eq_of_equiv_fin idealEquiv.symm

private def zeroPair (p : Fin 6 × Fin 6) : Prop :=
  (p.1 ≠ 5 ∧ p.2 ≠ 5) ∨ (p.1 = 5 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 = 5)

private instance (p : Fin 6 × Fin 6) : Decidable (zeroPair p) := by
  unfold zeroPair
  infer_instance

private theorem ideal_equiv_eq_bot (i : Fin 6) : idealEquiv i = ⊥ ↔ i = 0 :=
  idealEquiv.injective.eq_iff (b := 0)

private theorem native_product_zero (i j : Fin 6) :
    idealEquiv i * idealEquiv j = ⊥ ↔ zeroPair (i, j) := by
  by_cases hi : i = 5
  · subst i
    change (⊤ : Ideal R) * idealEquiv j = ⊥ ↔ zeroPair (5, j)
    simp [zeroPair, ideal_equiv_eq_bot]
  · by_cases hj : j = 5
    · subst j
      change idealEquiv i * (⊤ : Ideal R) = ⊥ ↔ zeroPair (i, 5)
      simp [zeroPair, hi, ideal_equiv_eq_bot]
    · have hle : idealEquiv i * idealEquiv j ≤ radical * radical :=
        Ideal.mul_mono (ideal_at_le_radical i hi) (ideal_at_le_radical j hj)
      have hsq : radical * radical = ⊥ := by simpa only [pow_two] using kerIdeal_sq K V
      rw [hsq] at hle
      exact iff_of_true (le_bot_iff.mp hle) (Or.inl ⟨hi, hj⟩)

private noncomputable def zeroProductEquiv :
    {I : Fin 2 → Ideal R // (∏ i, I i) = ⊥} ≃ {p : Fin 6 × Fin 6 // zeroPair p} :=
  Equiv.subtypeEquiv ((finTwoArrowEquiv (Ideal R)).trans
    (idealEquiv.symm.prodCongr idealEquiv.symm)) (fun I => by
      rw [Fin.prod_univ_two]
      change I 0 * I 1 = ⊥ ↔ zeroPair (idealEquiv.symm (I 0), idealEquiv.symm (I 1))
      rw [← native_product_zero, idealEquiv.apply_symm_apply, idealEquiv.apply_symm_apply])

private theorem zero_pair_card : Nat.card {p : Fin 6 × Fin 6 // zeroPair p} = 27 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

private theorem zero_product_card : Nat.card {I : Fin 2 → Ideal R // (∏ i, I i) = ⊥} = 27 :=
  (Nat.card_congr zeroProductEquiv).trans zero_pair_card

private theorem ordered_pair_card : Nat.card (Fin 2 → Ideal R) = 36 := by
  rw [Nat.card_fun, Nat.card_fin, ideal_card]
  decide

private theorem zeta_two : zeta R 2 = 1 - (1 : ℚ) / (2 : ℚ) ^ (2 : ℕ) := by
  have denominator : Nat.card (Ideal R) ^ 2 = 36 := by
    simpa only [Nat.card_fun, Nat.card_fin] using ordered_pair_card
  rw [zeta, zero_product_card, ← Nat.cast_pow, denominator]
  norm_num

private theorem witness_not_field : ¬ IsField R := by
  intro h
  let _ := h.isDomain
  have hx : emb a ≠ 0 := fun heq => not_a0 ((emb_eq_zero a).mp heq)
  exact hx ((mul_eq_zero.mp (inr_mul_inr K a a)).elim id id)

/-- The eight-element ring R has the field probability at k = 2 and is not a field. -/
theorem result : Not claim := by
  intro h
  let _ : Finite R := Nat.finite_of_card_ne_zero (by rw [ring_card]; decide)
  exact witness_not_field (h R 2 le_rfl zeta_two)

end D5.S0.Certificates.Algebra.ChakrabortyPatraIdealZeroProductRefutation
