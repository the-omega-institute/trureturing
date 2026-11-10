/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal canonical occupation coefficients for scalar lattice sewing. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
import Batteries.Tactic.OpenPrivate

/-! Literal factorial-coordinate sewing and occupation coefficients
of the original lattice fields.

proof_shape: canonical_sewing_summable: content
admission_basis: escape-witness
escape_witness: The actual finite word-field recurrence preserves complementary
row and factorial column bounds for arbitrary descendant words and signed modes.
Their product gives an ungrouped occupation majorant, before any cancellation
or energy-fibre grouping. Every private estimate is consumed by this theorem.
The factorial pairing is used only for coordinate resolution, not BPZ invariance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalOccupationSewing

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open LatticeAllStateField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FieldNormalProduct
open scoped BigOperators VertexOperator

open private creation_coefficient_norm creation_occupation_summable creation_coefficient_norm_le
  wordMap wordCoeff wordMap_nil wordCoeff_nil_add_single
  wordCoeff_cons occupation_sub_bounds rowWeight rowWeight_nonneg word_row_bound
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

noncomputable section

/-- The factorial coordinate-resolution form; no invariant BPZ property is asserted. -/
def H (D : LatticeData) (p t : Oscillator D) : ℂ :=
  FactorialFockMetric.inner p t

def A (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (d : Occ D) : ℂ :=
  H D p (canonical D α (β + γ) u (r + (level D d : ℤ)) (b D d)) *
    (H D (b D d) (canonical D β γ v (s - (level D d : ℤ)) w) /
      (FactorialFockMetric.weight d : ℂ))

def sewnTerm (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) : ℂ :=
  q ^ level D d * A D α β γ u v w p r s d

/-- The factorial occupation envelope for the complementary column estimate. -/
private def factorialEnvelope (D : LatticeData) (B : ℝ) (d : Occ D) : ℝ :=
  d.prod (fun x n => (B / (x.2 + 1 : ℝ)) ^ n) /
    (FactorialFockMetric.weight d : ℝ)

private theorem factorialEnvelope_nonneg (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (d : Occ D) : 0 ≤ factorialEnvelope D B d := by
  unfold factorialEnvelope
  apply div_nonneg
  · exact Finset.prod_nonneg (fun _ _ => pow_nonneg (div_nonneg hB (by positivity)) _)
  · exact Nat.cast_nonneg _

private theorem factorialEnvelope_add_single (D : LatticeData) (B : ℝ)
    (d : Occ D) (x : Index D) :
    factorialEnvelope D B (d + Finsupp.single x 1) * (d x + 1 : ℝ) =
      factorialEnvelope D B d * (B / (x.2 + 1 : ℝ)) := by
  classical
  have hw : (FactorialFockMetric.weight d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (FactorialFockMetric.weight_pos d)
  have hn : (d x + 1 : ℝ) ≠ 0 := by positivity
  unfold factorialEnvelope
  rw [Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _),
    FactorialFockMetric.weight_add_single]
  rw [Finsupp.prod_single_index (by simp)]
  simp only [pow_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem factorialEnvelope_sub_le (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (d : Occ D) (x : Index D) :
    factorialEnvelope D B (d - Finsupp.single x 1) ≤
      (1 + (level D d : ℝ)) * factorialEnvelope D B d := by
  classical
  have henv := factorialEnvelope_nonneg D B (by linarith) d
  by_cases hx : d x = 0
  · have heq : d - Finsupp.single x 1 = d := by
      ext y
      by_cases hy : y = x
      · subst y; simp [hx]
      · simp [hy]
    rw [heq]
    exact le_mul_of_one_le_left henv (by have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith)
  · let a := d - Finsupp.single x 1
    have hadd : a + Finsupp.single x 1 = d := Finsupp.sub_add_single_one_cancel hx
    have hd : a x + 1 = d x := by simpa using congrArg (fun c : Occ D => c x) hadd
    have hh := factorialEnvelope_add_single D B a x
    rw [hadd, show (a x + 1 : ℝ) = (d x : ℝ) by exact_mod_cast hd] at hh
    have hn : (x.2 + 1 : ℝ) ≠ 0 := by positivity
    have hrel : factorialEnvelope D B a * B =
        factorialEnvelope D B d * (d x : ℝ) * (x.2 + 1 : ℝ) := by
      have ht := congrArg (fun r : ℝ => r * (x.2 + 1 : ℝ)) hh
      field_simp at ht
      linarith
    have hlev : (d x : ℝ) * (x.2 + 1 : ℝ) ≤ (level D d : ℝ) := by
      have hs := Finset.single_le_sum (s := d.support)
        (f := fun y : Index D => d y * (y.2 + 1))
        (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)
      change d x * (x.2 + 1) ≤ level D d at hs
      exact_mod_cast hs
    calc
      _ ≤ factorialEnvelope D B a * B :=
        le_mul_of_one_le_right (factorialEnvelope_nonneg D B (by linarith) a) hB
      _ = _ := hrel
      _ ≤ (1 + (level D d : ℝ)) * factorialEnvelope D B d := by
        nlinarith

private theorem creation_factorialEnvelope (D : LatticeData) (α : Charge D)
    (B : ℝ) (hB : 0 ≤ B) (hα : ∀ i, ‖(α i : ℂ)‖ ≤ B) (t : ℤ) (d : Occ D) :
    ‖(creationCoeff D α t).coeff d‖ ≤ factorialEnvelope D B d := by
  classical
  apply (creation_coefficient_norm_le D α t d).trans
  rw [creation_coefficient_norm]
  unfold factorialEnvelope FactorialFockMetric.weight
  simp only [Finsupp.prod, Nat.cast_prod]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod₀
  · intro x hx; positivity
  · intro x hx
    gcongr
    exact hα x.1

/-- The actual translated field has the complementary factorial column envelope. -/
private theorem ground_column_bound (D : LatticeData) (α β : Charge D) :
    ∃ B L : ℝ, 1 ≤ B ∧ 1 ≤ L ∧ ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m d e‖ ≤
        L ^ e.degree * (1 + (level D d : ℝ)) ^ e.degree * factorialEnvelope D B d := by
  classical
  let B : ℝ := 1 + ∑ i : Fin D.rank, ‖(α i : ℂ)‖
  have hB : 1 ≤ B := by
    dsimp [B]
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun (i : Fin D.rank) _ => norm_nonneg (α i : ℂ))
    linarith
  have hα (i : Fin D.rank) : ‖(α i : ℂ)‖ ≤ B := by
    have hh := Finset.single_le_sum (fun (j : Fin D.rank) _ => norm_nonneg (α j : ℂ)) (Finset.mem_univ i)
    dsimp [B]
    linarith
  let T : Fin D.rank → ℝ := fun i => ‖(bilinear D α (unitCharge D i) : ℂ)‖
  let L : ℝ := 1 + ∑ i : Fin D.rank, T i
  have hL : 1 ≤ L := by
    dsimp [L, T]
    have hh := Finset.sum_nonneg (s := Finset.univ)
      (fun (i : Fin D.rank) _ => norm_nonneg (bilinear D α (unitCharge D i) : ℂ))
    linarith
  have hTx (x : Index D) : 1 + T x.1 ≤ L := by
    have hh := Finset.single_le_sum (fun (i : Fin D.rank) _ =>
      norm_nonneg (bilinear D α (unitCharge D i) : ℂ)) (Finset.mem_univ x.1)
    dsimp [L, T]
    linarith
  have hphase : ‖epsilon D α β‖ = 1 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  have hzero (d : Occ D) (m : ℤ) :
      ‖wordCoeff D α β [] m d 0‖ ≤ factorialEnvelope D B d := by
    have hc : LatticeActualProductKernel.convolution D α (-m - 1 - bilinear D α β) 1 =
        creationCoeff D α (-m - 1 - bilinear D α β) := by
      simpa using LatticeActualProductKernel.convolution_monomial D α
          (-m - 1 - bilinear D α β) 0 (1 : Oscillator D)
    have hh : wordCoeff D α β [] m d 0 =
        epsilon D α β * (creationCoeff D α (-m - 1 - bilinear D α β)).coeff d := by
      simp [wordCoeff, b, wordMap_nil, translatedPolynomial, hc]
    rw [hh, norm_mul, hphase, one_mul]
    exact creation_factorialEnvelope D α B (by linarith) hα _ d
  refine ⟨B, L, hB, hL, ?_⟩
  have haux : ∀ n : ℕ, ∀ e : Occ D, e.degree = n → ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D α β [] m d e‖ ≤
        L ^ e.degree * (1 + (level D d : ℝ)) ^ e.degree * factorialEnvelope D B d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he d m
      by_cases hz : e = 0
      · subst e
        simpa using hzero d m
      · obtain ⟨x, hx⟩ : ∃ x : Index D, e x ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (Finsupp.ext h)
        let e' := e - Finsupp.single x 1
        have hadd : e' + Finsupp.single x 1 = e := Finsupp.sub_add_single_one_cancel hx
        have hdeg : e'.degree + 1 = e.degree := by
          rw [← hadd, map_add, Finsupp.degree_single]
        have hi (d' : Occ D) (m' : ℤ) := ih e'.degree (by omega) e' rfl d' m'
        let N : ℝ := 1 + (level D d : ℝ)
        let V : ℝ := L ^ e'.degree * N ^ (e'.degree + 1) * factorialEnvelope D B d
        have hN : 1 ≤ N := by dsimp [N]; have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith
        have henv := factorialEnvelope_nonneg D B (by linarith) d
        have hV : 0 ≤ V := by dsimp [V]; positivity
        have hleft : ‖if x ∈ d.support then
            wordCoeff D α β [] m (d - Finsupp.single x 1) e' else 0‖ ≤ V := by
          split_ifs with hd
          · have henv' := factorialEnvelope_nonneg D B (by linarith)
              (d - Finsupp.single x 1)
            calc
              _ ≤ L ^ e'.degree * (1 + (level D (d - Finsupp.single x 1) : ℝ)) ^ e'.degree *
                  factorialEnvelope D B (d - Finsupp.single x 1) := hi _ _
              _ ≤ L ^ e'.degree * N ^ e'.degree * (N * factorialEnvelope D B d) := by
                gcongr
                · dsimp [N]; exact_mod_cast Nat.add_le_add_left (occupation_sub_bounds D d x).1 1
                · exact factorialEnvelope_sub_le D B hB d x
              _ = V := by dsimp [V]; rw [pow_succ]; ring
          · simpa only [norm_zero] using hV
        have hright : ‖wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) d e'‖ ≤ V := by
          exact (hi d _).trans (by dsimp [V]; gcongr; omega)
        rw [← hadd, wordCoeff_nil_add_single]
        calc
          _ ≤ ‖if x ∈ d.support then
              wordCoeff D α β [] m (d - Finsupp.single x 1) e' else 0‖ +
              ‖(bilinear D α (unitCharge D x.1) : ℂ) *
                wordCoeff D α β [] (m - (x.2 + 1 : ℕ)) d e'‖ := norm_sub_le _ _
          _ ≤ V + T x.1 * V := by
            rw [norm_mul]
            exact add_le_add hleft (mul_le_mul_of_nonneg_left hright (norm_nonneg _))
          _ = (1 + T x.1) * V := by ring
          _ ≤ L * V := mul_le_mul_of_nonneg_right (hTx x) hV
          _ = L ^ (e' + Finsupp.single x 1).degree *
              (1 + (level D d : ℝ)) ^ (e' + Finsupp.single x 1).degree * factorialEnvelope D B d := by
            rw [map_add, Finsupp.degree_single, pow_succ L]
            dsimp [V, N]
            ring
          _ ≤ _ := le_rfl
        all_goals exact le_rfl
  exact fun e d m => haux e.degree e rfl d m

private def columnWeight (D : LatticeData) (B : ℝ) (K : ℕ) (d : Occ D) : ℝ :=
  (1 + (level D d : ℝ)) ^ K * factorialEnvelope D B d

private theorem columnWeight_nonneg (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K : ℕ) (d : Occ D) : 0 ≤ columnWeight D B K d :=
  mul_nonneg (by positivity) (factorialEnvelope_nonneg D B (by linarith) d)

private theorem columnWeight_grow (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K J : ℕ) (hK : K ≤ J) (d : Occ D) :
    columnWeight D B K d ≤ columnWeight D B J d := by
  apply mul_le_mul_of_nonneg_right _ (factorialEnvelope_nonneg D B (by linarith) d)
  exact pow_le_pow_right₀ (by have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith) hK

private theorem columnWeight_sub_le (D : LatticeData) (B : ℝ) (hB : 1 ≤ B)
    (K : ℕ) (d : Occ D) (x : Index D) :
    columnWeight D B K (d - Finsupp.single x 1) ≤
      (1 + (level D d : ℝ)) * columnWeight D B K d := by
  have henv := factorialEnvelope_nonneg D B (by linarith) (d - Finsupp.single x 1)
  have henv' := factorialEnvelope_nonneg D B (by linarith) d
  dsimp [columnWeight]
  calc
    _ ≤ (1 + (level D d : ℝ)) ^ K *
        ((1 + (level D d : ℝ)) * factorialEnvelope D B d) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_left (occupation_sub_bounds D d x).1 1) K
      · exact factorialEnvelope_sub_le D B hB d x
      · exact henv
      · positivity
    _ = _ := by ring

/-- One actual normal-product insertion preserves the factorial column envelope. -/
private theorem word_column_step (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) (x : Index D) (B : ℝ) (hB : 1 ≤ B) (K : ℕ)
    (C : Occ D → ℝ) (hC : ∀ e, 0 ≤ C e)
    (hcol : ∀ (e d : Occ D) (m : ℤ),
      ‖wordCoeff D α β ω m d e‖ ≤ C e * columnWeight D B (K + e.degree) d) (e : Occ D) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D α β (x :: ω) m d e‖ ≤
        S * columnWeight D B ((K + (x.2 + 2)) + e.degree) d := by
  classical
  let Z : ℝ := ‖(bilinear D (unitCharge D x.1) β : ℂ)‖
  let T : ℕ → ℝ := fun j => (j.choose x.2 : ℝ) *
    (if j < x.2 then 0 else if j = x.2 then Z * C e
    else ‖((j : ℤ) - x.2 : ℂ)‖ *
      ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
        C (e - Finsupp.single (a, j - x.2 - 1) 1))
  let S : ℝ := ∑ j ∈ Finset.range (x.2 + level D e + 1), T j
  have hCe := hC e
  have hT (j : ℕ) : 0 ≤ T j := by
    dsimp [T]
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (norm_nonneg _) hCe
    · apply mul_nonneg (norm_nonneg _)
      exact Finset.sum_nonneg (fun a ha =>
        mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)) (hC _))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj => hT j)
  refine ⟨C e + S, add_nonneg hCe hS, ?_⟩
  intro d m
  let N : ℝ := 1 + (level D d : ℝ)
  let W : ℝ := columnWeight D B (K + e.degree) d
  have hW : 0 ≤ W := columnWeight_nonneg D B hB _ d
  have hN : 1 ≤ N := by dsimp [N]; have hh := Nat.cast_nonneg (α := ℝ) (level D d); linarith
  have hshift (a : Fin D.rank) (n : ℕ) (m' : ℤ) :
      ‖wordCoeff D α β ω m' d (e - Finsupp.single (a,n) 1)‖ ≤
        C (e - Finsupp.single (a,n) 1) * W :=
    (hcol _ d m').trans (mul_le_mul_of_nonneg_left
      (columnWeight_grow D B hB _ _ (Nat.add_le_add_left (occupation_sub_bounds D e (a,n)).2 K) d)
      (hC _))
  have hpos (j : ℕ) :
      ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
        (if j < x.2 then 0 else if j = x.2 then
          (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) d e
        else ((j : ℤ) - x.2 : ℂ) *
          ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (e (a, j - x.2 - 1) : ℂ) *
            wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1))‖ ≤
        T j * W := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast, T]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    split_ifs with hlt heq
    · simp
    · rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcol e d _) (norm_nonneg (bilinear D (unitCharge D x.1) β : ℂ))
    · rw [norm_mul, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ ∑ a : Fin D.rank,
            ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
              ‖wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (by simp))
        _ ≤ ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖ * (e (a, j - x.2 - 1) : ℝ) *
            (C (e - Finsupp.single (a, j - x.2 - 1) 1) * W) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hshift a _ _) (by positivity)
        _ = _ := by rw [Finset.sum_mul]; congr 1; funext a; ring
  have hneg (j : ℕ) (hj : j < level D d) :
      ‖((j + x.2).choose x.2 : ℂ) *
        if (x.1, j + x.2) ∈ d.support then
          wordCoeff D α β ω (m + j) (d - Finsupp.single (x.1, j + x.2) 1) e else 0‖ ≤
        C e * N ^ (x.2 + 1) * W := by
    have hchoose : ((j + x.2).choose x.2 : ℝ) ≤ N ^ x.2 := by
      calc
        _ ≤ (j + 1 : ℝ) ^ x.2 := by exact_mod_cast Nat.choose_add_le_add_one_pow j x.2
        _ ≤ N ^ x.2 := pow_le_pow_left₀ (by positivity)
          (by dsimp [N]; exact_mod_cast (show j + 1 ≤ 1 + level D d by omega)) _
    rw [norm_mul, Complex.norm_natCast]
    split_ifs with hd
    · have hh := (hcol e _ (m + j)).trans
        (mul_le_mul_of_nonneg_left (columnWeight_sub_le D B hB _ d (x.1, j + x.2)) hCe)
      calc
        _ ≤ N ^ x.2 * (C e * (N * W)) :=
          mul_le_mul hchoose hh (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    · simp only [norm_zero, mul_zero]; positivity
  rw [wordCoeff_cons]
  calc
    _ ≤ (∑ j ∈ Finset.range (level D d),
        ‖((j + x.2).choose x.2 : ℂ) *
          if (x.1, j + x.2) ∈ d.support then
            wordCoeff D α β ω (m + j) (d - Finsupp.single (x.1, j + x.2) 1) e else 0‖) +
      ∑ j ∈ Finset.range (x.2 + level D e + 1),
        ‖(-1 : ℂ) ^ x.2 * (j.choose x.2 : ℂ) *
          (if j < x.2 then 0 else if j = x.2 then
            (bilinear D (unitCharge D x.1) β : ℂ) * wordCoeff D α β ω (m - j - 1) d e
          else ((j : ℤ) - x.2 : ℂ) *
            ∑ a : Fin D.rank, (D.G x.1 a : ℂ) * (e (a, j - x.2 - 1) : ℂ) *
              wordCoeff D α β ω (m - j - 1) d (e - Finsupp.single (a, j - x.2 - 1) 1))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ (level D d : ℝ) * (C e * N ^ (x.2 + 1) * W) + S * W := by
      apply add_le_add
      · exact (Finset.sum_le_sum (fun j hj => hneg j (Finset.mem_range.mp hj))).trans (by simp)
      · rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun j hj => hpos j)
    _ ≤ N * (C e * N ^ (x.2 + 1) * W) + S * W := by
      gcongr
      dsimp [N]
      linarith
    _ = C e * columnWeight D B ((K + (x.2 + 2)) + e.degree) d + S * W := by
      dsimp [columnWeight, W, N]
      rw [show K + (x.2 + 2) + e.degree = (K + e.degree) + (x.2 + 2) by omega]
      simp only [pow_add, pow_succ, pow_one]
      ring
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (columnWeight_grow D B hB _ _ (by omega) d) hS)

/-- Every actual descendant word has a factorial column envelope in every signed mode. -/
private theorem word_column_bound (D : LatticeData) (α β : Charge D) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ω : List (Index D), ∃ K : ℕ, ∀ e : Occ D,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Occ D) (m : ℤ),
        ‖wordCoeff D α β ω m d e‖ ≤ C * columnWeight D B (K + e.degree) d := by
  classical
  obtain ⟨B, L, hB, hL, hbase⟩ := ground_column_bound D α β
  refine ⟨B, hB, ?_⟩
  intro ω
  induction ω with
  | nil =>
    refine ⟨0, fun e => ⟨L ^ e.degree, by positivity, ?_⟩⟩
    intro d m
    simpa [columnWeight, mul_assoc] using hbase e d m
  | cons x ω ih =>
    obtain ⟨K, hi⟩ := ih
    choose C hC hb using hi
    exact ⟨K + (x.2 + 2), fun e => word_column_step D α β ω x B hB K C hC hb e⟩

private theorem factorialEnvelope_mul (D : LatticeData) (L B : ℝ) (d : Occ D) :
    L ^ d.degree * factorialEnvelope D B d = factorialEnvelope D (L * B) d := by
  classical
  have hdegree : L ^ d.degree = d.prod (fun _ n => L ^ n) := by
    simp [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  rw [hdegree]
  unfold factorialEnvelope Finsupp.prod
  rw [← mul_div_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  rw [← mul_pow]
  congr 1
  ring

private theorem factorialEnvelope_creation (D : LatticeData) (B : ℝ) (d : Occ D) :
    factorialEnvelope D B d = B ^ d.degree *
      ‖(creationCoeff D (fun _ => 1) (level D d)).coeff d‖ := by
  classical
  have hdegree : B ^ d.degree = d.prod (fun _ n => B ^ n) := by
    simp [Finsupp.degree_apply, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
  rw [creation_coefficient_norm, hdegree]
  simp only [Int.cast_one, norm_one]
  unfold factorialEnvelope FactorialFockMetric.weight Finsupp.prod
  rw [Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x hx
  simp only [div_pow, one_pow]
  ring

private theorem factorialEnvelope_summable (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q‖ ^ level D d * factorialEnvelope D B d) := by
  have hs := creation_occupation_summable D (fun _ => 1) B hB q hq
  simpa only [factorialEnvelope_creation, norm_mul, norm_pow, mul_left_comm, mul_comm,
    mul_assoc] using hs

private theorem polynomial_geometric_bound (K : ℕ) (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 + (n : ℝ)) ^ K * x ^ n ≤ C := by
  have hg := summable_geometric_of_lt_one hx hx1
  have hp := summable_pow_mul_geometric_of_norm_lt_one K
    (r := x) (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)
  refine ⟨2 ^ (K - 1) * ((∑' n : ℕ, x ^ n) + (∑' n : ℕ, (n : ℝ) ^ K * x ^ n)),
    mul_nonneg (by positivity) (add_nonneg
      (tsum_nonneg (fun _ => pow_nonneg hx _))
      (tsum_nonneg (fun _ => mul_nonneg (by positivity) (pow_nonneg hx _)))), ?_⟩
  intro n
  calc
    _ ≤ (2 ^ (K - 1) * (1 ^ K + (n : ℝ) ^ K)) * x ^ n :=
      mul_le_mul_of_nonneg_right (add_pow_le (by positivity) (by positivity) K)
        (pow_nonneg hx _)
    _ = 2 ^ (K - 1) * (x ^ n + (n : ℝ) ^ K * x ^ n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (hg.le_tsum n (fun _ _ => pow_nonneg hx _))
        (hp.le_tsum n (fun _ _ => mul_nonneg (by positivity) (pow_nonneg hx _)))) (by positivity)

/-- Polynomial energy factors preserve summability of the factorial occupation envelope. -/
private theorem polynomial_factorialEnvelope_summable (D : LatticeData) (B : ℝ) (hB : 0 ≤ B)
    (K : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q‖ ^ level D d *
      (1 + (level D d : ℝ)) ^ K * factorialEnvelope D B d) := by
  obtain ⟨ρ, hqρ, hρ1⟩ := exists_between hq
  have hρ0 : 0 < ρ := lt_of_le_of_lt (norm_nonneg q) hqρ
  have hx0 : 0 ≤ ‖q‖ / ρ := div_nonneg (norm_nonneg q) hρ0.le
  have hx1 : ‖q‖ / ρ < 1 := (div_lt_one hρ0).mpr hqρ
  obtain ⟨C, hC, hb⟩ := polynomial_geometric_bound K (‖q‖ / ρ) hx0 hx1
  have hs := factorialEnvelope_summable D B hB (ρ : ℂ)
    (by simpa [abs_of_pos hρ0] using hρ1)
  have hs' : Summable (fun d : Occ D => C * (ρ ^ level D d * factorialEnvelope D B d)) := by
    simpa [abs_of_pos hρ0] using hs.mul_left C
  refine hs'.of_nonneg_of_le (fun d => by
    exact mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg q) _) (by positivity))
      (factorialEnvelope_nonneg D B hB d)) ?_
  intro d
  have hh := mul_le_mul_of_nonneg_right (hb (level D d))
    (mul_nonneg (pow_nonneg hρ0.le (level D d)) (factorialEnvelope_nonneg D B hB d))
  calc
    _ = ((1 + (level D d : ℝ)) ^ K * (‖q‖ / ρ) ^ level D d) *
        (ρ ^ level D d * factorialEnvelope D B d) := by
      rw [div_pow]
      field_simp
    _ ≤ _ := hh

/-- Ungrouped absolute summability for any two actual descendant words,
with arbitrary signed mode choices depending on the occupation. -/
private theorem word_contraction_summable (D : LatticeData) (α β γ : Charge D)
    (ω ν : List (Index D)) (e f : Occ D) (m n : Occ D → ℤ)
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ level D d *
      wordCoeff D α (β + γ) ω (m d) e d * wordCoeff D β γ ν (n d) d f‖) := by
  obtain ⟨L, hL, hr⟩ := word_row_bound D α (β + γ)
  obtain ⟨K, hr⟩ := hr ω
  obtain ⟨C, hC, hr⟩ := hr e
  obtain ⟨B, hB, hc⟩ := word_column_bound D β γ
  obtain ⟨J, hc⟩ := hc ν
  obtain ⟨S, hS, hc⟩ := hc f
  have hLB : 0 ≤ L * B := mul_nonneg (by linarith) (by linarith)
  have hs := (polynomial_factorialEnvelope_summable D (L * B) hLB
    (K + (J + f.degree)) q hq).mul_left (C * S)
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro d
  rw [norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ ‖q‖ ^ level D d * (C * rowWeight D L K d) *
        (S * columnWeight D B (J + f.degree) d) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hr d (m d)) (pow_nonneg (norm_nonneg q) _))
        (hc d (n d)) (norm_nonneg _)
        (mul_nonneg (pow_nonneg (norm_nonneg q) _)
          (mul_nonneg hC (rowWeight_nonneg D L hL K d)))
    _ = _ := by
      dsimp [rowWeight, columnWeight]
      rw [pow_add, ← factorialEnvelope_mul]
      ring


private theorem polynomial_expansion (D : LatticeData) (p : Oscillator D) :
    p = ∑ e ∈ p.support, p.coeff e • b D e := by
  simpa only [b, smul_monomial, smul_eq_mul, mul_one] using p.as_sum

private theorem canonical_monomial_word (D : LatticeData) (α β : Charge D)
    (U : Occ D) (m : ℤ) (p : Oscillator D) :
    canonical D α β (b D U) m p = wordMap D α β (occurrences D U) m p := by
  change ((((Y D (Finsupp.single α (b D U)))[[m]]) (Finsupp.single β p)) (α + β)) = _
  rw [show b D U = monomial U (1 : ℂ) from rfl, stateField_monomial]
  rfl

private theorem canonical_coefficient_expansion (D : LatticeData) (α β : Charge D)
    (u w : Oscillator D) (m : ℤ) (e : Occ D) :
    (canonical D α β u m w).coeff e =
      ∑ U ∈ u.support, ∑ W ∈ w.support,
        (u.coeff U * w.coeff W) * wordCoeff D α β (occurrences D U) m e W := by
  classical
  conv_lhs => rw [polynomial_expansion D u, polynomial_expansion D w]
  simp only [map_sum, map_smul, Finset.sum_apply, LinearMap.sum_apply,
    Pi.smul_apply, LinearMap.smul_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    smul_eq_mul, canonical_monomial_word, Finset.mul_sum, wordCoeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro W hW
  ring

private theorem canonical_basis_input_expansion (D : LatticeData) (α β : Charge D)
    (u : Oscillator D) (m : ℤ) (e d : Occ D) :
    (canonical D α β u m (b D d)).coeff e =
      ∑ U ∈ u.support, u.coeff U * wordCoeff D α β (occurrences D U) m e d := by
  classical
  rw [canonical_coefficient_expansion]
  simp [b]

private theorem inner_coefficient_expansion (D : LatticeData) (p t : Oscillator D) :
    H D p t = ∑ P ∈ p.support,
      (FactorialFockMetric.weight P : ℂ) * star (p.coeff P) * t.coeff P := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [H, FactorialFockMetric.inner, map_sum, sum_inner]
  exact Finset.sum_congr rfl (fun P hP =>
    FactorialFockMetric.inner_monomial_left P (p.coeff P) t)

private theorem inner_basis_coordinate (D : LatticeData) (d : Occ D) (t : Oscillator D) :
    H D (b D d) t / (FactorialFockMetric.weight d : ℂ) = t.coeff d := by
  have hw : (FactorialFockMetric.weight d : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (FactorialFockMetric.weight_pos d))
  simp [H, b, FactorialFockMetric.inner_monomial_left, hw]

/-- The literal sewing term is a finite external-state expansion of the actual word contractions.
No internal occupation is truncated or grouped. -/
private theorem sewnTerm_expansion (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (d : Occ D) :
    sewnTerm D α β γ u v w p r s q d =
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ W ∈ w.support,
        ((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * w.coeff W) *
        (q ^ level D d *
          wordCoeff D α (β + γ) (occurrences D U) (r + (level D d : ℤ)) P d *
          wordCoeff D β γ (occurrences D V) (s - (level D d : ℤ)) d W) := by
  classical
  unfold sewnTerm A
  rw [inner_basis_coordinate, inner_coefficient_expansion,
    canonical_coefficient_expansion]
  simp only [canonical_basis_input_expansion, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := w.support) (t := p.support)]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := w.support) (t := u.support),
    Finset.sum_comm (s := v.support) (t := u.support)]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro W hW
  ring

/-- Absolute summability of the ungrouped literal canonical occupation contraction,
for all external oscillator polynomials, signed offsets and open-disk parameters.
The factorial form supplies coordinate resolution; BPZ invariance is not asserted. -/
theorem canonical_sewing_summable (D : LatticeData) (α β γ : Charge D)
    (u v w p : Oscillator D) (r s : ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖sewnTerm D α β γ u v w p r s q d‖) := by
  classical
  have hs : Summable (fun d : Occ D =>
      ∑ P ∈ p.support, ∑ U ∈ u.support, ∑ V ∈ v.support, ∑ W ∈ w.support,
        ‖((FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
            u.coeff U * v.coeff V * w.coeff W) *
          (q ^ level D d *
            wordCoeff D α (β + γ) (occurrences D U) (r + (level D d : ℤ)) P d *
            wordCoeff D β γ (occurrences D V) (s - (level D d : ℤ)) d W)‖) := by
    apply summable_sum
    intro P hP
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    apply summable_sum
    intro W hW
    simpa only [norm_mul] using
      (word_contraction_summable D α β γ (occurrences D U) (occurrences D V) P W
        (fun d => r + (level D d : ℤ)) (fun d => s - (level D d : ℤ)) q hq).mul_left
        ‖(FactorialFockMetric.weight P : ℂ) * star (p.coeff P) *
          u.coeff U * v.coeff V * w.coeff W‖
  refine hs.of_nonneg_of_le (fun d => norm_nonneg _) ?_
  intro d
  rw [sewnTerm_expansion]
  apply norm_sum_le_of_le
  intro P hP
  apply norm_sum_le_of_le
  intro U hU
  apply norm_sum_le_of_le
  intro V hV
  exact norm_sum_le _ _


#print axioms canonical_sewing_summable
#print axioms word_contraction_summable
#print axioms word_column_bound
#print axioms ground_column_bound

end
end D5.S3.VertexAlgebra.CanonicalOccupationSewing
