/- GID: D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced hypercube rendezvous has a dimension-independent quantum gap. -/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
open scoped BigOperators symmDiff ComplexOrder
namespace D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
abbrev Vertex (d : ℕ) := Finset (Fin d)
abbrev Output (d t : ℕ) := {A : Vertex d // A.card = t}
abbrev Correlation (d t : ℕ) := Vertex d → Vertex d → Output d t → Output d t → ℝ
def Promised (d t : ℕ) (σ τ : Vertex d) : Prop := (σ ∆ τ).card = 2 * t
def Inputs (d t : ℕ) : Finset (Vertex d × Vertex d) := by
  classical
  exact Finset.univ.filter (fun p => Promised d t p.1 p.2)
def Wins {d t : ℕ} (σ τ : Vertex d) (A B : Output d t) : Prop :=
  Disjoint A.val B.val ∧ A.val ∪ B.val = σ ∆ τ
def value {d t : ℕ} (P : Correlation d t) : ℝ := by
  classical
  exact (∑ p ∈ Inputs d t, ∑ A, ∑ B, if Wins p.1 p.2 A B then P p.1 p.2 A B else 0) /
    ((Inputs d t).card : ℝ)
structure QStrategy (d t : ℕ) (α : Type*) (β : Type*)
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] where
  ρ : Matrix (α × β) (α × β) ℂ
  rho_psd : ρ.PosSemidef
  rho_trace : Matrix.trace ρ = 1
  E : Vertex d → Output d t → Matrix α α ℂ
  F : Vertex d → Output d t → Matrix β β ℂ
  E_psd : ∀ σ A, (E σ A).PosSemidef
  F_psd : ∀ τ B, (F τ B).PosSemidef
  E_sum : ∀ σ, (∑ A, E σ A) = 1
  F_sum : ∀ τ, (∑ B, F τ B) = 1
def QStrategy.prob {d t : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : QStrategy d t α β) : Correlation d t := fun σ τ A B =>
  (Matrix.trace (S.ρ * Matrix.kronecker (S.E σ A) (S.F τ B))).re
def IsQuantum {d t : ℕ} (P : Correlation d t) : Prop :=
  ∃ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
      (dα : DecidableEq α) (dβ : DecidableEq β),
    letI : Fintype α := fα
    letI : Fintype β := fβ
    letI : DecidableEq α := dα
    letI : DecidableEq β := dβ
    ∃ S : QStrategy d t α β, S.prob = P
def IsNS {d t : ℕ} (P : Correlation d t) : Prop :=
  (∀ σ τ A B, 0 ≤ P σ τ A B) ∧ (∀ σ τ, (∑ A, ∑ B, P σ τ A B) = 1) ∧
  (∀ σ τ τ' A, (∑ B, P σ τ A B) = ∑ B, P σ τ' A B) ∧
  (∀ σ σ' τ B, (∑ A, P σ τ A B) = ∑ A, P σ' τ A B)
def QValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsQuantum P ∧ value P = r}
def NSValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsNS P ∧ value P = r}
def omegaQ (d t : ℕ) : ℝ := sSup (QValues d t)
def omegaNS (d t : ℕ) : ℝ := sSup (NSValues d t)
def claim : Prop := ∀ t d : ℕ, 2 ≤ t → 2 * t < d → omegaQ d t < omegaNS d t
private def n (d t : ℕ) : ℝ := (Nat.choose d t : ℝ)
private def kappa (d t : ℕ) : ℝ :=
  1 / ((n d t) ^ 4 * (4 * Real.sqrt 2 * (t : ℝ) + 2) ^ 2)

private lemma disjoint_extension {d t : ℕ} (S : Vertex d) (hc : S.card + t ≤ d) :
    ∃ B : Output d t, Disjoint S B.val := by
  obtain ⟨B, hB, hb⟩ := Finset.exists_subset_card_eq
    (show t ≤ (Finset.univ \ S).card by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp only [Finset.card_univ, Fintype.card_fin]; omega)
  exact ⟨⟨B, hb⟩, Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp (hB hy)).2 hx)⟩
private lemma exchange_reduction {d t : ℕ} (A R : Output d t) (h : A ≠ R) :
    ∃ A' : Output d t, (A'.val \ R.val).card + 1 = (A.val \ R.val).card ∧
      (A.val ∪ A'.val).card ≤ t + 1 := by
  have hc := Finset.card_sdiff_comm (A.property.trans R.property.symm)
  have hp : 0 < (A.val \ R.val).card := by
    by_contra hn
    have hs : A.val ⊆ R.val := Finset.sdiff_eq_empty_iff_subset.mp
      (Finset.card_eq_zero.mp (show (A.val \ R.val).card = 0 by omega))
    exact h (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [A.property, R.property])))
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hp
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (R.val \ A.val).card by omega)
  have haA := (Finset.mem_sdiff.mp ha).1
  have hbR := (Finset.mem_sdiff.mp hb).1
  have hbA := (Finset.mem_sdiff.mp hb).2
  let T := insert b (A.val.erase a)
  have hT : T.card = t := by
    rw [Finset.card_insert_of_notMem (by simp [hbA]), Finset.card_erase_of_mem haA, A.property]
    have := Finset.card_pos.mpr ⟨a, haA⟩; rw [A.property] at this; omega
  have he : T \ R.val = (A.val \ R.val).erase a := by
    ext x; simp only [T, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx | hx, hr⟩
      · exact False.elim (hr (hx ▸ hbR))
      · exact ⟨hx.1, hx.2, hr⟩
    · rintro ⟨hx, hxA, hr⟩; exact ⟨Or.inr ⟨hx, hxA⟩, hr⟩
  refine ⟨⟨T, hT⟩, ?_, ?_⟩
  · change (T \ R.val).card + 1 = _; rw [he]; exact Finset.card_erase_add_one ha
  · have hs : A.val ∪ T ⊆ insert b A.val := by
      intro x hx; rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_insert_of_mem hx
      · rcases Finset.mem_insert.mp hx with hx | hx
        · exact Finset.mem_insert.mpr (Or.inl hx)
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mp hx).2
    exact (Finset.card_le_card hs).trans (by rw [Finset.card_insert_of_notMem hbA, A.property])
private lemma symmDiff_card {d : ℕ} (S T : Vertex d) :
    (S ∆ T).card + 2 * (S ∩ T).card = S.card + T.card := by
  have hd : Disjoint (S \ T) (T \ S) := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1)
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at h2; omega
private lemma common_sphere {d t : ℕ} (ht : 2 ≤ t) (hd : 2 * t < d)
    (ζ ζ' : Vertex d) (hz : ζ.card = t ∨ ζ.card = t - 2)
    (hz' : ζ'.card = t ∨ ζ'.card = t - 2) (hne : ζ ≠ ζ') :
    ∃ (σ : Vertex d) (A A' : Output d t), A ≠ A' ∧ σ ∆ A.val = ζ ∧ σ ∆ A'.val = ζ' := by
  let D := ζ ∆ ζ'
  have hc := symmDiff_card ζ ζ'
  have he : ∃ s, D.card = 2 * s ∧ s ≤ t := by
    refine ⟨D.card / 2, ?_, ?_⟩ <;>
      (change D.card + 2 * (ζ ∩ ζ').card = ζ.card + ζ'.card at hc;
       rcases hz with hz | hz <;> rcases hz' with hz' | hz' <;> omega)
  obtain ⟨s, hs, hst⟩ := he
  obtain ⟨U, hU, hu⟩ := Finset.exists_subset_card_eq (show s ≤ D.card by omega)
  obtain ⟨W, hW, hw⟩ := Finset.exists_subset_card_eq
    (show t - s ≤ (Finset.univ \ D).card by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ D)]
      simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hUW : Disjoint U W := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp (hW hy)).2 (hU hx))
  let T := U ∪ W
  have hT : T.card = t := by rw [Finset.card_union_of_disjoint hUW, hu, hw]; omega
  have hi : T ∩ D = U := by
    ext x; constructor
    · intro hx; rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hu | hw
      · exact hu
      · exact False.elim ((Finset.mem_sdiff.mp (hW hw)).2 (Finset.mem_inter.mp hx).2)
    · intro hx; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, hU hx⟩
  have hT' : (T ∆ D).card = t := by have := symmDiff_card T D; rw [hi, hu, hT, hs] at this; omega
  refine ⟨ζ ∆ T, ⟨T, hT⟩, ⟨T ∆ D, hT'⟩, ?_, by simp, ?_⟩
  · intro ha; have ha' := congrArg Subtype.val ha
    have hD := congrArg (fun X => T ∆ X) ha'
    rw [symmDiff_self, symmDiff_symmDiff_cancel_left] at hD
    exact hne (Finset.symmDiff_eq_empty.mp hD.symm)
  · simp [← symmDiff_assoc, D]
private lemma large_family {d t : ℕ} (ht : 2 ≤ t) (hd : 2 * t < d) :
    ∃ J : Finset (Vertex d), J.card = Nat.choose d t + 1 ∧
      ∀ ζ ∈ J, ζ.card = t ∨ ζ.card = t - 2 := by
  obtain ⟨K, _, hk⟩ := Finset.exists_subset_card_eq
    (show t - 2 ≤ (Finset.univ : Vertex d).card by simp; omega)
  let S := (Finset.univ : Vertex d).powersetCard t
  have hn : K ∉ S := by intro h; have := (Finset.mem_powersetCard.mp h).2; omega
  refine ⟨insert K S, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hn, Finset.card_powersetCard]; simp
  · intro ζ hz; rcases Finset.mem_insert.mp hz with hz | hz
    · exact Or.inr (hz ▸ hk)
    · exact Or.inl (Finset.mem_powersetCard.mp hz).2

private lemma winning_translate {d t : ℕ} (ζ : Vertex d) (A B : Output d t)
    (hab : Disjoint A.val B.val) : Wins (ζ ∆ A.val) (ζ ∆ B.val) A B := by
  refine ⟨hab, ?_⟩
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self]
  exact (Finset.symmDiff_eq_union hab).symm.trans (bot_symmDiff _).symm
section AbstractGap
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (C : PreInnerProductSpace.Core ℝ V)
private lemma form_symm (x y : V) : C.inner x y = C.inner y x := by
  simpa using C.conj_inner_symm y x
private lemma form_sub (x y : V) :
    C.inner (x - y) (x - y) = C.inner x x - 2 * C.inner x y + C.inner y y := by
  have he := @InnerProductSpace.Core.inner_sub_sub_self ℝ V _ _ _ C x y
  rw [form_symm C y x] at he; linarith
private lemma form_cs (x y : V) : (C.inner x y) ^ 2 ≤ C.inner x x * C.inner y y := by
  have he := @InnerProductSpace.Core.inner_mul_inner_self_le ℝ V _ _ _ C x y
  rw [form_symm C y x] at he
  simpa only [Real.norm_eq_abs, ← sq, sq_abs, RCLike.re_to_real] using he
private lemma form_bound (x y : V) :
    C.inner x y ≤ Real.sqrt (C.inner x x) * Real.sqrt (C.inner y y) := by
  have he := @InnerProductSpace.Core.norm_inner_le_norm ℝ V _ _ _ C x y
  change |C.inner x y| ≤ Real.sqrt (C.inner x x) * Real.sqrt (C.inner y y) at he
  exact (le_abs_self _).trans he
private lemma form_triangle (x y z : V) :
    Real.sqrt (C.inner (x - z) (x - z)) ≤
      Real.sqrt (C.inner (x - y) (x - y)) + Real.sqrt (C.inner (y - z) (y - z)) := by
  let _ := C
  let _ := InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ) (F := V)
  have he := norm_add_le (x - y) (y - z)
  rw [sub_add_sub_cancel] at he; exact he
private lemma form_sum {ι : Type*} (S : Finset ι) (f : ι → V) (x : V) :
    C.inner x (∑ i ∈ S, f i) = ∑ i ∈ S, C.inner x (f i) := by
  classical
  induction S using Finset.induction_on
  · exact @InnerProductSpace.Core.inner_zero_right ℝ V _ _ _ C x
  · rename_i a S ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      @InnerProductSpace.Core.inner_add_right ℝ V _ _ _ C, ih]
private lemma exchange_transport {d t : ℕ} (X : Output d t → V) (e : ℝ) (he : 0 ≤ e)
    (step : ∀ A A' : Output d t, (A.val ∪ A'.val).card ≤ t + 1 →
      Real.sqrt (C.inner (X A - X A') (X A - X A')) ≤ 2 * e) (A R : Output d t) :
    Real.sqrt (C.inner (X A - X R) (X A - X R)) ≤ 2 * (t : ℝ) * e := by
  have bound : ∀ k (A : Output d t), (A.val \ R.val).card = k →
      Real.sqrt (C.inner (X A - X R) (X A - X R)) ≤ 2 * (k : ℝ) * e := by
    intro k
    induction k using Nat.strong_induction_on
    rename_i k ih
    intro A hk
    by_cases hAR : A = R
    · subst A; rw [sub_self, @InnerProductSpace.Core.inner_zero_right ℝ V _ _ _ C, Real.sqrt_zero]
      positivity
    · obtain ⟨A', hcard, hUnion⟩ := exchange_reduction A R hAR
      have hlt : (A'.val \ R.val).card < k := by omega
      have hrec := ih _ hlt A' rfl
      have htri := form_triangle C (X A) (X A') (X R)
      have hstep := step A A' hUnion
      have hcast : ((A'.val \ R.val).card : ℝ) + 1 = k := by exact_mod_cast hcard.trans hk
      nlinarith
  have hb := bound _ A rfl
  have hc : ((A.val \ R.val).card : ℝ) ≤ t := by
    exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans_eq A.property
  nlinarith
private lemma scalar_gap {d t : ℕ} (hn : 1 ≤ n d t) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hg : 1 ≤ (n d t) ^ 2 * (4 * (t : ℝ) * Real.sqrt (2 * δ) + 2 * δ)) :
    kappa d t ≤ δ := by
  have hs := Real.sq_sqrt h0
  have hr := Real.sqrt_nonneg δ
  have hδ : δ ≤ Real.sqrt δ := by nlinarith
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hg
  let a := 4 * Real.sqrt 2 * (t : ℝ) + 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hg' : 1 ≤ (n d t) ^ 2 * a * Real.sqrt δ := by
    dsimp only [a]; nlinarith [mul_nonneg (sq_nonneg (n d t)) (sub_nonneg.mpr hδ)]
  have hg2 : 1 ≤ ((n d t) ^ 2 * a * Real.sqrt δ) ^ 2 := by nlinarith
  have hid : ((n d t) ^ 2 * a * Real.sqrt δ) ^ 2 = ((n d t) ^ 4 * a ^ 2) * δ := by
    rw [mul_pow, mul_pow, hs]; ring
  rw [hid] at hg2
  have hd : 0 < (n d t) ^ 4 * a ^ 2 := by positivity
  change 1 / ((n d t) ^ 4 * a ^ 2) ≤ δ
  exact (div_le_iff₀ hd).mpr (by simpa only [one_mul, mul_comm] using hg2)
end AbstractGap
end D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
