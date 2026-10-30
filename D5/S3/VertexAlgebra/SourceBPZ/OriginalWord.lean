/- GID: D5/S3/VertexAlgebra/SourceBPZ/OriginalWord
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/OriginalWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labelled original word BPZ induction and finite source-flow bridge. -/

import D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
import D5.S3.VertexAlgebra.LatticeAllStateField
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import D5.S3.VertexAlgebra.SourceMobius.Coordinates
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents FieldNormalProduct LatticeAllStateField
open LatticePositiveEnergy
open LatticeHalfFockFiniteCorrection (sourceWeight wordWeight)
open SourceMobius

/-! A choice keeps a finite labelled occurrence at an order in `0..n`, where
zero deletes the occurrence and positive values lower it to that order. -/

def WordChoice (D : LatticeData) : List (Index D) → Type
  | [] => PUnit
  | x :: w => Fin (x.2 + 2) × WordChoice D w

instance wordChoiceFinite (D : LatticeData) (w : List (Index D)) : Finite (WordChoice D w) := by
  induction w with
  | nil => change Finite PUnit; infer_instance
  | cons x w ih => change Finite (Fin (x.2 + 2) × WordChoice D w); infer_instance

instance wordChoiceFintype (D : LatticeData) (w : List (Index D)) : Fintype (WordChoice D w) :=
  by
    induction w with
    | nil => change Fintype PUnit; infer_instance
    | cons x w ih => change Fintype (Fin (x.2 + 2) × WordChoice D w); infer_instance

def choiceLower (D : LatticeData) : {w : List (Index D)} → WordChoice D w → List (Index D)
  | [], _ => []
  | x :: w, c =>
      if c.1.val = 0 then choiceLower D c.2
      else (x.1, c.1.val - 1) :: choiceLower D c.2

def choiceRetained (D : LatticeData) : {w : List (Index D)} → WordChoice D w → ℕ
  | [], _ => 0
  | x :: w, c => c.1.val + choiceRetained D c.2

def choiceCoefficient (D : LatticeData) (α : Charge D) :
    {w : List (Index D)} → WordChoice D w → ℂ
  | [], _ => 1
  | x :: w, c =>
      (if c.1.val = 0 then (bilinear D (unitCharge D x.1) α : ℂ)
       else ((x.2 + 1).choose c.1.val : ℂ)) * choiceCoefficient D α c.2

def transposeReadout (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (α : Charge D) : (w : List (Index D)) → ℤ → Carrier D → Carrier D → ℂ
  | w, m, u, v =>
      ∑ c ∈ (Finset.univ : Finset (WordChoice D w)),
        choiceCoefficient D α c *
          B u (((wordField D α (choiceLower D c))[[
            2 * chargeEnergy D α + (wordWeight D w : ℤ) +
              (choiceRetained D c : ℤ) - m - 2]]) v)

theorem word_choice_charge (D : LatticeData) (α β : Charge D)
    (w : List (Index D)) (n : ℤ) (v : Oscillator D) :
    ∃ p : Oscillator D,
      ((wordField D α w)[[n]]) (Finsupp.single β v) = Finsupp.single (α + β) p := by
  classical
  have neutral (x : Index D) (m : ℤ) (δ : Charge D) (p : Oscillator D) :
      ∃ q : Oscillator D,
        ((dividedDerivative x.2 (neutralField D x.1))[[m]])
            (Finsupp.single δ p) = Finsupp.single δ q := by
    refine ⟨((Ring.choose (-m - 1 + x.2) x.2 : ℤ) : ℂ) •
        neutralPolynomialMode D x.1 δ (m - x.2) p, ?_⟩
    change Ring.choose (-m - 1 + x.2) x.2 •
      HVertexOperator.coeff (neutralField D x.1) (-m - 1 + x.2)
        (Finsupp.single δ p) = _
    rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff, neutralMode_single,
      show -(-m - 1 + x.2) - 1 = m - x.2 by omega]
    simp only [LinearMap.smul_apply, ← Finsupp.smul_single, Int.cast_smul_eq_zsmul]
  induction w generalizing n β v with
  | nil =>
      rw [wordField, actualField, VertexOperator.ncoeff_of_coeff,
        (actual_creation_coefficient_transport D α α).2.2.1]
      refine ⟨epsilon D α β • ∑ d ∈ (translatedPolynomial D α v).support,
        (translatedPolynomial D α v).coeff d •
          creationCoeff D α (-n - 1 - bilinear D α β + d), ?_⟩
      simp [rawSingle]
  | cons x tail ih =>
      rw [wordField, (normalMinusOne _ _).2]
      have left : ∃ p : Oscillator D,
          (∑ᶠ j : ℕ,
            ((dividedDerivative x.2 (neutralField D x.1))[[ -(j : ℤ) - 1]])
              (((wordField D α tail)[[n + j]]) (Finsupp.single β v))) =
            Finsupp.single (α + β) p := by
        refine finsum_induction (fun z => ∃ p : Oscillator D,
            z = Finsupp.single (α + β) p) ?_ ?_ ?_
        · exact ⟨0, by simp⟩
        · intro a b ha hb
          obtain ⟨p, hp⟩ := ha
          obtain ⟨q, hq⟩ := hb
          refine ⟨p + q, ?_⟩
          rw [hp, hq, ← Finsupp.single_add]
        · intro j
          obtain ⟨r, hr⟩ := ih (n := n + j) (β := β) v
          obtain ⟨s, hs⟩ := neutral x (-(j : ℤ) - 1) (α + β) r
          refine ⟨s, ?_⟩
          rw [hr, hs]
      have right : ∃ p : Oscillator D,
          (∑ᶠ j : ℕ,
            ((wordField D α tail)[[n - j - 1]])
              (((dividedDerivative x.2 (neutralField D x.1))[[j]])
                (Finsupp.single β v))) =
            Finsupp.single (α + β) p := by
        refine finsum_induction (fun z => ∃ p : Oscillator D,
            z = Finsupp.single (α + β) p) ?_ ?_ ?_
        · exact ⟨0, by simp⟩
        · intro a b ha hb
          obtain ⟨p, hp⟩ := ha
          obtain ⟨q, hq⟩ := hb
          refine ⟨p + q, ?_⟩
          rw [hp, hq, ← Finsupp.single_add]
        · intro j
          obtain ⟨r, hr⟩ := neutral x j β v
          obtain ⟨s, hs⟩ := ih (n := n - j - 1) (β := β) r
          refine ⟨s, ?_⟩
          rw [hr, hs]
      obtain ⟨p, hp⟩ := left
      obtain ⟨q, hq⟩ := right
      refine ⟨p + q, ?_⟩
      rw [hp, hq, ← Finsupp.single_add]

private theorem zero_single (D : LatticeData) (i : Fin D.rank)
    (β : Charge D) (p : Oscillator D) :
    neutralMode D i 0 (Finsupp.single β p) =
      (bilinear D (unitCharge D i) β : ℂ) • Finsupp.single β p := by
  simp [neutralMode_single, neutralPolynomialMode, Finsupp.smul_single]

private theorem word_zero (D : LatticeData) (α : Charge D)
    (w : List (Index D)) (t : ℤ) (z : Carrier D) (i : Fin D.rank) :
    neutralMode D i 0 (((wordField D α w)[[t]]) z) =
      ((wordField D α w)[[t]]) (neutralMode D i 0 z) +
        (bilinear D (unitCharge D i) α : ℂ) • ((wordField D α w)[[t]]) z := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add β p z absent nonzero ih =>
      obtain ⟨q, hq⟩ := word_choice_charge D α β w t p
      have hb : (bilinear D (unitCharge D i) (α + β) : ℂ) =
          (bilinear D (unitCharge D i) α : ℂ) +
            (bilinear D (unitCharge D i) β : ℂ) := by
        simp [bilinear, mul_add, Finset.sum_add_distrib]
      simp only [map_add, map_smul, smul_add, zero_single, hq, ih, hb, add_smul]
      abel

private theorem choice_cons_sum (D : LatticeData) (x : Index D)
    (w : List (Index D)) {M : Type*} [AddCommMonoid M]
    (f : WordChoice D (x :: w) → M) :
    (∑ c : WordChoice D (x :: w), f c) =
      ∑ c : WordChoice D w,
        (f (0, c) + ∑ r : Fin (x.2 + 1), f (r.succ, c)) := by
  change (∑ c : Fin (x.2 + 2) × WordChoice D w, f c) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.sum_comm,
    ← Finset.sum_add_distrib]

private theorem transposeReadout_cons (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (x : Index D) (w : List (Index D)) (m : ℤ) (u v : Carrier D) :
    transposeReadout D B α (x :: w) m u v =
      ∑ c : WordChoice D w, choiceCoefficient D α c *
        ((∑ s ∈ Finset.range (x.2 + 1), ((x.2 + 1).choose (s + 1) : ℂ) *
          B u (((insertion D x.1 s (wordField D α (choiceLower D c)))[[
            (2 * chargeEnergy D α + (wordWeight D w : ℤ) +
              (choiceRetained D c : ℤ) - 2) + x.2 + s + 2 - m]]) v)) +
          (bilinear D (unitCharge D x.1) α : ℂ) *
          B u (((wordField D α (choiceLower D c))[[
            (2 * chargeEnergy D α + (wordWeight D w : ℤ) +
              (choiceRetained D c : ℤ) - 2) + x.2 + 1 - m]]) v)) := by
  classical
  unfold transposeReadout
  rw [choice_cons_sum]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [choiceCoefficient, choiceLower, choiceRetained, Fin.val_zero,
    Fin.val_succ, Nat.succ_ne_zero, if_pos, if_false, Nat.add_sub_cancel,
    zero_add, wordWeight, List.map_cons, List.sum_cons, sourceWeight,
    Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  rw [Fin.sum_univ_eq_sum_range]
  have hm (s : ℕ) :
      2 * chargeEnergy D α + ((x.2 : ℤ) + 1 + (wordWeight D w : ℤ)) +
          ((s : ℤ) + 1 + (choiceRetained D c : ℤ)) - m - 2 =
        (2 * chargeEnergy D α + (wordWeight D w : ℤ) +
          (choiceRetained D c : ℤ) - 2) + x.2 + s + 2 - m := by ring
  have hz : 2 * chargeEnergy D α + ((x.2 : ℤ) + 1 + (wordWeight D w : ℤ)) +
      (choiceRetained D c : ℤ) - m - 2 =
        (2 * chargeEnergy D α + (wordWeight D w : ℤ) +
          (choiceRetained D c : ℤ) - 2) + x.2 + 1 - m := by ring
  simp only [hm, hz, wordField, insertion]
  rw [mul_add, Finset.mul_sum]
  conv_rhs => rw [add_comm]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro s hs
    ring

theorem actual_word_transpose (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hcurrent : ∀ i : Fin D.rank, ∀ k x y,
      B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (hprimary : ∀ t x y, B (((actualField D α)[[t]]) x) y =
      paritySign (chargeEnergy D α) *
        B x (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) y)) :
    ∀ (w : List (Index D)) (m : ℤ) (u v : Carrier D),
    B (((wordField D α w)[[m]]) u) v =
      paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D w) *
        transposeReadout D B α w m u v := by
  intro w
  induction w with
  | nil =>
      intro m u v
      simp only [transposeReadout, wordWeight, WordChoice, Fintype.sum_unique,
        choiceCoefficient, choiceLower, choiceRetained, mul_one, add_zero,
        Int.cast_zero, sub_zero, pow_zero, one_mul]
      simpa [wordField] using hprimary m u v
  | cons x tail ih =>
      intro m u v
      let S : Finset (WordChoice D tail) :=
        @Finset.univ (WordChoice D tail) (wordChoiceFintype D tail)
      let G : WordChoice D tail → VertexOperator ℂ (Carrier D) :=
        fun c => wordField D α (choiceLower D c)
      let K : WordChoice D tail → ℤ := fun c =>
        2 * chargeEnergy D α + (wordWeight D tail : ℤ) +
          (choiceRetained D c : ℤ) - 2
      have htail : ∀ t x' y', B (((wordField D α tail)[[t]]) x') y' =
          ∑ c ∈ S, (paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D tail) *
            choiceCoefficient D α c) * B x' (((G c)[[K c - t]]) y') := by
        intro t x' y'
        rw [ih t x' y']
        unfold transposeReadout
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        have hm : K c - t =
            2 * chargeEnergy D α + (wordWeight D tail : ℤ) +
              (choiceRetained D c : ℤ) - t - 2 := by
          dsimp [K]
          ring
        rw [hm]
        simp [S, G]
        ring
      have hzero : ∀ c ∈ S, ∀ t z,
          neutralMode D x.1 0 (((G c)[[t]]) z) =
            ((G c)[[t]]) (neutralMode D x.1 0 z) +
              (bilinear D (unitCharge D x.1) α : ℂ) • (((G c)[[t]]) z) := by
        intro c hc t z
        exact word_zero D α (choiceLower D c) t z x.1
      have h := consumed_normal_product_form D B x.1 (hcurrent x.1) x.2
        (wordField D α tail) S G
        (fun c => paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D tail) *
          choiceCoefficient D α c) K (bilinear D (unitCharge D x.1) α : ℂ)
        htail hzero m u v
      change B (((insertion D x.1 x.2 (wordField D α tail))[[m]]) u) v = _
      rw [h, transposeReadout_cons]
      simp only [wordWeight, List.map_cons, List.sum_cons, sourceWeight, pow_add]
      simp only [S, G, K, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring


/- The scalar rectangle uses genuine current cutoffs. All currents moved onto
an input have nonnegative modes, so the same bounds survive every step. -/
private abbrev WordCutoff (D : LatticeData) (U : ℕ) (u : Carrier D) : Prop :=
  ∀ (i : Fin D.rank) (k : ℤ), (U : ℤ) ≤ k → neutralMode D i k u = 0

private theorem current_same_sign (D : LatticeData) (i j : Fin D.rank)
    (k l : ℤ) (h : (k < 0 ∧ l < 0) ∨ (0 ≤ k ∧ 0 ≤ l)) (u : Carrier D) :
    neutralMode D i k (neutralMode D j l u) =
      neutralMode D j l (neutralMode D i k u) := by
  have hc := congrArg (fun f : Module.End ℂ (Carrier D) => f u)
    (neutralMode_heisenberg D i j k l)
  have hz : (if k + l = 0 then (k : ℂ) * (D.G i j : ℂ) else 0) = 0 := by
    split_ifs with he
    · have hk : k = 0 := by rcases h with h | h <;> omega
      simp [hk]
    · rfl
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hz,
    zero_smul, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc

private theorem cutoff_current (D : LatticeData) (U : ℕ) (u : Carrier D)
    (hu : WordCutoff D U u) (i : Fin D.rank) (k : ℤ) (hk : 0 ≤ k) :
    WordCutoff D U (neutralMode D i k u) := by
  intro j l hl
  rw [current_same_sign D j i l k (Or.inr ⟨by omega, hk⟩), hu j l hl, map_zero]

private def coefficient (p : ℕ) (k : ℤ) : ℂ :=
  ((Ring.choose (-k-1) p : ℤ) : ℂ)

private theorem derivative_mode (D : LatticeData) (i : Fin D.rank) (p : ℕ) (m : ℤ) :
    ((dividedDerivative p (neutralField D i))[[m]]) =
      coefficient p (m-p) • neutralMode D i (m-p) := by
  apply LinearMap.ext
  intro v
  change Ring.choose (-m-1+p) p •
    HVertexOperator.coeff (neutralField D i) (-m-1+p) v = _
  rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff]
  rw [show -(-m-1+p)-1 = m-p by omega]
  simp only [coefficient, LinearMap.smul_apply, Int.cast_smul_eq_zsmul]
  congr 2; omega

private theorem coefficient_zero_band (p : ℕ) (k : ℤ)
    (hk : -(p : ℤ) ≤ k) (hn : k < 0) : coefficient p k = 0 := by
  have ha : 0 ≤ -k-1 := by omega
  obtain ⟨a, he⟩ := Int.eq_ofNat_of_zero_le ha
  have hb : a < p := by omega
  simp [coefficient, he, Ring.choose_natCast, Nat.choose_eq_zero_of_lt hb]

private theorem forward_finite (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D) :
    Function.HasFiniteSupport (fun t : ℕ => (L[[-(t : ℤ)-1]]) ((F[[m+t]]) u)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (F u)).order-m).toNat, ?_⟩
  intro t ht
  contrapose! ht
  have hz : (F[[m+t]]) u = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private theorem reverse_finite (D : LatticeData) (L F : VertexOperator ℂ (Carrier D))
    (m : ℤ) (u : Carrier D) :
    Function.HasFiniteSupport (fun t : ℕ => (F[[m-t-1]]) ((L[[t]]) u)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm (L u)).order-1).toNat, ?_⟩
  intro t ht
  contrapose! ht
  have hz : (L[[t]]) u = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  simp [hz]

private theorem scalar_offsets (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D)) (m : ℤ)
    (A C : ℕ) (hA : 0 < A) (hC : 0 < C)
    (u v : Carrier D) (hu : WordCutoff D A u) (hv : WordCutoff D C v) :
    B (((insertion D i p F)[[m]]) u) v =
      (∑ t ∈ Finset.range (C),
        coefficient p (-(t : ℤ)-1-p) *
          B (neutralMode D i (-(t : ℤ)-1-p) ((F[[m+t]]) u)) v) +
      ∑ t ∈ Finset.range (A+p),
        coefficient p ((t : ℤ)-p) *
          B ((F[[m-t-1]]) (neutralMode D i ((t : ℤ)-p) u)) v := by
  let L := dividedDerivative p (neutralField D i)
  rw [insertion, (normalMinusOne L F).2]
  change (B.flip v) (_+_) = _
  rw [map_add, map_finsum (B.flip v) (forward_finite D L F m u),
    map_finsum (B.flip v) (reverse_finite D L F m u)]
  simp only [L, derivative_mode, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply,
    map_smul, smul_eq_mul]
  congr 1
  · apply finsum_eq_sum_of_support_subset
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra ho
    have hz : neutralMode D i (-(-(t : ℤ)-1-p)) v = 0 := by
      exact hv i _ (by omega)
    exact ht (by dsimp only; rw [hB, hz, map_zero, neg_zero, mul_zero])
  · apply finsum_eq_sum_of_support_subset
    intro t ht
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra ho
    have hz : neutralMode D i ((t : ℤ)-p) u = 0 := by
      exact hu i _ (by omega)
    exact ht (by dsimp only; simp [hz])

/- Both scalar intervals are independent of the tail field and the derivative
order. The omitted derivative bands vanish by integer binomial coefficients. -/
private theorem scalar_interval (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (i : Fin D.rank)
    (hB : ∀ k x y, B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (p : ℕ) (F : VertexOperator ℂ (Carrier D)) (m : ℤ)
    (A C : ℕ) (hA : 0 < A) (hC : 0 < C)
    (u v : Carrier D) (hu : WordCutoff D A u) (hv : WordCutoff D C v) :
    B (((insertion D i p F)[[m]]) u) v =
      (∑ k ∈ Finset.Icc (1-(C : ℤ)) (-1),
        coefficient p k * B (neutralMode D i k ((F[[m-k-p-1]]) u)) v) +
      ∑ k ∈ Finset.Icc 0 ((A : ℤ)-1),
        coefficient p k * B ((F[[m-k-p-1]]) (neutralMode D i k u)) v := by
  rw [scalar_offsets D B i hB p F m A C hA hC u v hu hv]
  congr 1
  · apply Finset.sum_bij_ne_zero (fun (t : ℕ) _ _ => -(t : ℤ)-1-p)
    · intro t ht hn
      rw [Finset.mem_Icc]
      constructor
      · by_contra ho
        have hz : neutralMode D i (-(-(t : ℤ)-1-p)) v = 0 := by
          exact hv i _ (by omega)
        exact hn (by rw [hB, hz, map_zero, neg_zero, mul_zero])
      · omega
    · intro a ha hna b hb hnb he
      omega
    · intro k hk hn
      have hk' := Finset.mem_Icc.mp hk
      have below : k < -(p : ℤ) := by
        by_contra ho
        exact hn (by rw [coefficient_zero_band p k (by omega) (by omega), zero_mul])
      refine ⟨(-k-1-p).toNat, ?_, ?_, ?_⟩
      · rw [Finset.mem_range]
        have hc := hC
        omega
      · have he : (((-k-1-p).toNat : ℕ) : ℤ) = -k-1-p :=
          Int.toNat_of_nonneg (by omega)
        simpa only [he, show -(-k-1-p)-1-(p : ℤ) = k by omega,
          show m+(-k-1-p) = m-k-p-1 by omega] using hn
      · have he := Int.toNat_of_nonneg (show 0 ≤ -k-1-p by omega)
        omega
    · intro t ht hn
      simp only [show m-(-(t : ℤ)-1-p)-p-1 = m+t by omega]
  · apply Finset.sum_bij_ne_zero (fun (t : ℕ) _ _ => (t : ℤ)-p)
    · intro t ht hn
      have ht' := Finset.mem_range.mp ht
      rw [Finset.mem_Icc]
      constructor
      · by_contra ho
        exact hn (by rw [coefficient_zero_band p ((t : ℤ)-p) (by omega) (by omega),
          zero_mul])
      · omega
    · intro a ha hna b hb hnb he
      omega
    · intro k hk hn
      have hk' := Finset.mem_Icc.mp hk
      refine ⟨(k+p).toNat, ?_, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · have he : (((k+p).toNat : ℕ) : ℤ) = k+p := Int.toNat_of_nonneg (by omega)
        simpa only [he, show k+(p : ℤ)-p = k by omega,
          show m-(k+p)-1 = m-k-p-1 by omega] using hn
      · have he := Int.toNat_of_nonneg (show 0 ≤ k+p by omega)
        omega
    · intro t ht hn
      simp only [show m-((t : ℤ)-p)-p-1 = m-t-1 by omega]


private def moveLeft (D : LatticeData) (i : Fin D.rank) (k : ℤ)
    (u : Carrier D) : Carrier D := if k < 0 then u else neutralMode D i k u

private def moveRight (D : LatticeData) (i : Fin D.rank) (k : ℤ)
    (v : Carrier D) : Carrier D := if k < 0 then neutralMode D i (-k) v else v

private def scalarStep (D : LatticeData) (A C : ℕ) (x : Index D)
    (f : ℤ → Carrier D → Carrier D → ℂ) (m : ℤ) (u v : Carrier D) : ℂ :=
  ∑ k ∈ Finset.Icc (1 - (C : ℤ)) ((A : ℤ) - 1),
    (if k < 0 then -coefficient x.2 k else coefficient x.2 k) *
      f (m - k - x.2 - 1) (moveLeft D x.1 k u) (moveRight D x.1 k v)

private theorem scalar_insertion_step (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (A C : ℕ) (hA : 0 < A) (hC : 0 < C) (x : Index D)
    (F : VertexOperator ℂ (Carrier D)) (m : ℤ) (u v : Carrier D)
    (hu : WordCutoff D A u) (hv : WordCutoff D C v) :
    B (((insertion D x.1 x.2 F)[[m]]) u) v =
      scalarStep D A C x (fun n a b => B ((F[[n]]) a) b) m u v := by
  rw [scalar_interval D B x.1 (hc x.1) x.2 F m A C hA hC u v hu hv]
  unfold scalarStep
  have split : Finset.Icc (1 - (C : ℤ)) ((A : ℤ) - 1) =
      Finset.Icc (1 - (C : ℤ)) (-1) ∪ Finset.Icc 0 ((A : ℤ) - 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [split, Finset.sum_union (by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have := Finset.mem_Icc.mp hk
    have := Finset.mem_Icc.mp hl
    omega)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hn : k < 0 := by have := Finset.mem_Icc.mp hk; omega
    simp only [moveLeft, moveRight, if_pos hn, hc]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    have hn : ¬ k < 0 := by have := Finset.mem_Icc.mp hk; omega
    simp only [moveLeft, moveRight, if_neg hn]

private def scalarWord (D : LatticeData) (A C : ℕ)
    (f : ℤ → Carrier D → Carrier D → ℂ) :
    List (Index D) → ℤ → Carrier D → Carrier D → ℂ
  | [], m, u, v => f m u v
  | x :: w, m, u, v => scalarStep D A C x (scalarWord D A C f w) m u v

private theorem word_scalar_rectangle (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (A C : ℕ) (hA : 0 < A) (hC : 0 < C)
    (w : List (Index D)) (m : ℤ) (u v : Carrier D)
    (hu : WordCutoff D A u) (hv : WordCutoff D C v) :
    B (((wordField D α w)[[m]]) u) v =
      scalarWord D A C (fun n a b => B (((actualField D α)[[n]]) a) b) w m u v := by
  induction w generalizing m u v with
  | nil => rfl
  | cons x w ih =>
      change B (((insertion D x.1 x.2 (wordField D α w))[[m]]) u) v = _
      rw [scalar_insertion_step D B hc A C hA hC x _ m u v hu hv]
      change scalarStep D A C x _ m u v = scalarStep D A C x _ m u v
      unfold scalarStep
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      apply ih
      · unfold moveLeft
        split_ifs with hn
        · exact hu
        · exact cutoff_current D A u hu x.1 k (by omega)
      · unfold moveRight
        split_ifs with hn
        · exact cutoff_current D C v hv x.1 (-k) (by omega)
        · exact hv

private theorem moveLeft_commute (D : LatticeData) (i j : Fin D.rank)
    (k l : ℤ) (u : Carrier D) :
    moveLeft D j l (moveLeft D i k u) = moveLeft D i k (moveLeft D j l u) := by
  unfold moveLeft
  split_ifs with hk hl <;> try rfl
  exact current_same_sign D j i l k (Or.inr ⟨by omega, by omega⟩) u

private theorem moveRight_commute (D : LatticeData) (i j : Fin D.rank)
    (k l : ℤ) (u : Carrier D) :
    moveRight D j l (moveRight D i k u) = moveRight D i k (moveRight D j l u) := by
  unfold moveRight
  split_ifs with hk hl <;> try rfl
  exact current_same_sign D j i (-l) (-k) (Or.inr ⟨by omega, by omega⟩) u

private theorem scalarStep_commute (D : LatticeData) (A C : ℕ)
    (x y : Index D) (f : ℤ → Carrier D → Carrier D → ℂ)
    (m : ℤ) (u v : Carrier D) :
    scalarStep D A C x (scalarStep D A C y f) m u v =
      scalarStep D A C y (scalarStep D A C x f) m u v := by
  unfold scalarStep
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro k hk
  rw [moveLeft_commute, moveRight_commute,
    show m - k - x.2 - 1 - l - y.2 - 1 =
      m - l - y.2 - 1 - k - x.2 - 1 by omega]
  ring

private theorem scalarWord_perm (D : LatticeData) (A C : ℕ)
    (f : ℤ → Carrier D → Carrier D → ℂ) {w z : List (Index D)}
    (h : w.Perm z) : scalarWord D A C f w = scalarWord D A C f z := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [scalarWord, ih]
  | swap x y w =>
      funext m u v
      exact scalarStep_commute D A C _ _ _ m u v
  | trans h h' ih ih' => exact ih.trans ih'

private theorem word_readout_perm (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    {w z : List (Index D)} (h : w.Perm z) (m : ℤ) (u v : Carrier D) :
    B (((wordField D α w)[[m]]) u) v = B (((wordField D α z)[[m]]) u) v := by
  let A := vectorFrequencyBound D u + 1
  let C := vectorFrequencyBound D v + 1
  have hu : WordCutoff D A u := by
    intro i k hk
    exact neutralMode_vanish D i u k (by dsimp [A] at hk; omega)
  have hv : WordCutoff D C v := by
    intro i k hk
    exact neutralMode_vanish D i v k (by dsimp [C] at hk; omega)
  rw [word_scalar_rectangle D B α hc A C (by simp [A]) (by simp [C]) w m u v hu hv,
    word_scalar_rectangle D B α hc A C (by simp [A]) (by simp [C]) z m u v hu hv,
    scalarWord_perm D A C _ h]

private theorem current_flip (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v)) :
    ∀ i : Fin D.rank, ∀ k u v,
      B.flip (neutralMode D i k u) v = -B.flip u (neutralMode D i (-k) v) := by
  intro i k u v
  have h := hc i (-k) v u
  simp only [neg_neg] at h
  change B v (neutralMode D i k u) = -B (neutralMode D i (-k) v) u
  linear_combination h

private def wordPolynomial (D : LatticeData) (w : List (Index D)) : Oscillator D :=
  (w.map MvPolynomial.X).prod

private theorem word_Y (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (w : List (Index D)) (m : ℤ) (u v : Carrier D) :
    B (((wordField D α w)[[m]]) u) v =
      B (((Y D (Finsupp.single α (wordPolynomial D w)))[[m]]) u) v := by
  classical
  let e : Index D →₀ ℕ := (w : Multiset (Index D)).toFinsupp
  have hp : w.Perm (occurrences D e) := by
    apply Multiset.coe_eq_coe.mp
    simp [occurrences, e, Multiset.toFinsupp_toMultiset]
  have hpoly : wordPolynomial D w = MvPolynomial.monomial e 1 := by
    unfold wordPolynomial
    rw [(hp.map MvPolynomial.X).prod_eq, occurrences_product]
  rw [word_readout_perm D B α hc hp, hpoly, stateField_monomial]

private theorem right_word_Y (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (w : List (Index D)) (m : ℤ) (u v : Carrier D) :
    B u (((wordField D α w)[[m]]) v) =
      B u (((Y D (Finsupp.single α (wordPolynomial D w)))[[m]]) v) :=
  word_Y D B.flip α (current_flip D B hc) w m v u


private theorem choice_bounds (D : LatticeData) {w : List (Index D)}
    (c : WordChoice D w) : choiceRetained D c ≤ wordWeight D w ∧
      wordWeight D (choiceLower D c) = choiceRetained D c := by
  induction w with
  | nil => simp [choiceRetained, choiceLower, wordWeight]
  | cons x w ih =>
      rcases c with ⟨r, c⟩
      obtain ⟨hle, heq⟩ := ih c
      have hr := r.isLt
      simp only [choiceRetained, choiceLower, wordWeight, List.map_cons,
        List.sum_cons, sourceWeight]
      split_ifs with hz
      · simp [hz, heq, hle]
      · simp only [List.map_cons, List.sum_cons, sourceWeight, heq]
        constructor <;> omega

private theorem flow_X_polynomial (D : LatticeData) (α : Charge D)
    (i : Fin D.rank) (p : ℕ) :
    flowPolynomial D α (MvPolynomial.X (i,p)) =
      (∑ r ∈ Finset.range (p + 1), Polynomial.monomial (p-r)
        (((p+1).choose (r+1) : ℂ) • (MvPolynomial.X (i,r) : Oscillator D))) +
      Polynomial.monomial (p+1) (MvPolynomial.C (bilinear D (unitCharge D i) α : ℂ)) := by
  classical
  have hd : MvPolynomial.weightedTotalDegree (sourceWeight D)
      (MvPolynomial.X (i,p) : Oscillator D) = p+1 := by
    rw [MvPolynomial.weightedTotalDegree, MvPolynomial.support_X]
    simp [sourceWeight, Finsupp.weight_single]
  have hk := sectorL1_degree_bound D α (MvPolynomial.X (i,p))
  rw [hd] at hk
  rw [flowPolynomial_eq_sum D α _ (p+1) hk, Finset.sum_range_succ,
    variable_power_charge]
  have hf : ((p+1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p+1)
  simp only [smul_smul, inv_mul_cancel₀ hf, one_smul]
  congr 1
  calc
    _ = ∑ n ∈ Finset.range (p+1), Polynomial.monomial n
        (((p+1).choose n : ℂ) • (MvPolynomial.X (i,p-n) : Oscillator D)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [variable_power D α i p n (by have := Finset.mem_range.mp hn; omega),
        smul_smul, Nat.descFactorial_eq_factorial_mul_choose]
      congr 1
      congr 1
      have hn' : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      push_cast
      field_simp
    _ = _ := by
      rw [← Finset.sum_range_reflect (fun n => Polynomial.monomial n
        (((p+1).choose n : ℂ) • (MvPolynomial.X (i,p-n) : Oscillator D))) (p+1)]
      apply Finset.sum_congr rfl
      intro r hr
      have hr' : r ≤ p := by have := Finset.mem_range.mp hr; omega
      have he : p - (p-r) = r := by omega
      have hc : (p+1).choose (p-r) = (p+1).choose (r+1) := by
        apply Nat.choose_symm_of_eq_add
        omega
      simp only [Nat.add_sub_cancel, he, hc]

private theorem flow_word_choices (D : LatticeData) (α : Charge D)
    (w : List (Index D)) :
    flowPolynomial D α (wordPolynomial D w) =
      ∑ c : WordChoice D w,
        Polynomial.monomial (wordWeight D w - choiceRetained D c)
          (choiceCoefficient D α c • wordPolynomial D (choiceLower D c)) := by
  classical
  induction w with
  | nil => simp [wordPolynomial, wordWeight, WordChoice, choiceRetained,
      choiceCoefficient, choiceLower]
  | cons x w ih =>
      have hp : wordPolynomial D (x :: w) = MvPolynomial.X x * wordPolynomial D w := rfl
      rw [hp, map_mul, ih, flow_X_polynomial, choice_cons_sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hb := (choice_bounds D c).1
      simp only [choiceRetained, choiceCoefficient, choiceLower, Fin.val_zero,
        Fin.val_succ, Nat.succ_ne_zero, if_pos, if_false, Nat.add_sub_cancel,
        wordPolynomial, List.map_cons, List.prod_cons, wordWeight,
        List.map_cons, List.sum_cons, sourceWeight, zero_add]
      rw [Fin.sum_univ_eq_sum_range, add_mul, Finset.sum_mul]
      rw [add_comm]
      congr 1
      · have he : x.2 + 1 + (wordWeight D w) - choiceRetained D c =
            (x.2 + 1) + (wordWeight D w - choiceRetained D c) := by omega
        rw [he, Polynomial.monomial_mul_monomial]
        congr 1
        simp only [MvPolynomial.smul_eq_C_mul, map_mul]
        ring
      · apply Finset.sum_congr rfl
        intro r hr
        have hr' := Finset.mem_range.mp hr
        have he : x.2 + 1 + wordWeight D w - (r+1+choiceRetained D c) =
            (x.2-r) + (wordWeight D w - choiceRetained D c) := by omega
        rw [he, Polynomial.monomial_mul_monomial]
        congr 1
        simp only [MvPolynomial.smul_eq_C_mul, map_mul]
        ring

private theorem choice_divided_power (D : LatticeData) (hu : IsUnit D.G.det)
    (α : Charge D) (w : List (Index D)) (l : ℕ) :
    (l.factorial : ℂ)⁻¹ •
        (sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
          (Finsupp.single α (wordPolynomial D w)) =
      ∑ c : WordChoice D w,
        if wordWeight D w - choiceRetained D c = l then
          choiceCoefficient D α c • Finsupp.single α (wordPolynomial D (choiceLower D c))
        else 0 := by
  classical
  rw [sugawara_pow_single D _ (Matrix.nonsing_inv_mul _ (gram_det_unit D hu))
    (Matrix.mul_nonsing_inv _ (gram_det_unit D hu)), Finsupp.smul_single,
    ← flowPolynomial_coeff, flow_word_choices, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finsupp.single_finsetSum]
  apply Finset.sum_congr rfl
  intro c hc
  split_ifs <;> simp [Finsupp.smul_single]

private theorem parity_weight (q : ℤ) (R : ℕ) :
    paritySign q * (-1 : ℂ)^R = paritySign (q + (R : ℤ)) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [pow_succ, ← mul_assoc, ih]
      have he : Even (q + ((R+1 : ℕ) : ℤ)) ↔ ¬ Even (q + (R : ℤ)) := by
        rw [Nat.cast_add, Nat.cast_one, Int.even_add_one]
      unfold paritySign
      split_ifs <;> simp_all

private def rightReadout (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (m : ℤ) (u v : Carrier D) : Carrier D →ₗ[ℂ] ℂ where
  toFun a := B u (((Y D a)[[m]]) v)
  map_add' a b := by
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c a := by
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

private theorem word_bpz (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hp : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (α : Charge D) (w : List (Index D)) (m : ℤ) (u v : Carrier D) :
    B (((Y D (Finsupp.single α (wordPolynomial D w)))[[m]]) u) v =
      paritySign (chargeEnergy D α + (wordWeight D w : ℤ)) *
        ∑ l ∈ Finset.range (wordWeight D w + 1), (l.factorial : ℂ)⁻¹ *
          B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
            (Finsupp.single α (wordPolynomial D w))))[[
              2 * (chargeEnergy D α + (wordWeight D w : ℤ)) - l - m - 2]]) v) := by
  classical
  rw [← word_Y D B α hc, actual_word_transpose D B α hc (hp α), parity_weight]
  congr 1
  unfold transposeReadout
  have term (l : ℕ) :
      (l.factorial : ℂ)⁻¹ *
        B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
          (Finsupp.single α (wordPolynomial D w))))[[
            2 * (chargeEnergy D α + (wordWeight D w : ℤ)) - l - m - 2]]) v) =
        ∑ c : WordChoice D w, if wordWeight D w - choiceRetained D c = l then
          choiceCoefficient D α c * B u (((wordField D α (choiceLower D c))[[
            2 * chargeEnergy D α + (wordWeight D w : ℤ) +
              (choiceRetained D c : ℤ) - m - 2]]) v) else 0 := by
    let t := 2 * (chargeEnergy D α + (wordWeight D w : ℤ)) - l - m - 2
    change (l.factorial : ℂ)⁻¹ • rightReadout D B t u v
      ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
        (Finsupp.single α (wordPolynomial D w))) = _
    rw [← map_smul, choice_divided_power, map_sum]
    apply Finset.sum_congr rfl
    intro c hc'
    split_ifs with he
    · rw [map_smul]
      change _ * B u (((Y D (Finsupp.single α (wordPolynomial D (choiceLower D c))))[[t]]) v) = _
      rw [← right_word_Y D B α hc]
      congr 3
      have hb := (choice_bounds D c).1
      dsimp [t]
      omega
    · simp
  simp_rw [term]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc'
  have hb := (choice_bounds D c).1
  simp [show wordWeight D w - choiceRetained D c < wordWeight D w + 1 by omega]


private theorem occurrences_weight (D : LatticeData) (e : Index D →₀ ℕ) :
    wordWeight D (occurrences D e) = e.weight (sourceWeight D) := by
  classical
  unfold wordWeight occurrences
  rw [Multiset.sum_map_toList]
  induction e using Finsupp.induction with
  | zero => simp
  | single_add x n e absent nonzero ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add,
        Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.sum_nsmul,
        Multiset.map_singleton, Multiset.sum_singleton, ih]
      simp [map_add, Finsupp.weight_single, nsmul_eq_mul]

private def oppositeReadout (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (N : ℕ) (d m : ℤ) (u v : Carrier D) : Carrier D →ₗ[ℂ] ℂ :=
  paritySign d • ∑ l ∈ Finset.range N, (l.factorial : ℂ)⁻¹ •
    (rightReadout D B (2*d-l-m-2) u v).comp
      (sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)

private theorem basis_bpz_bound (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hc : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hp : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (α : Charge D) (e : Index D →₀ ℕ) (N : ℕ) (d m : ℤ)
    (hd : chargeEnergy D α + (e.weight (sourceWeight D) : ℤ) = d)
    (hN : e.weight (sourceWeight D) + 1 ≤ N) (u v : Carrier D) :
    rightReadout D B.flip m v u (Finsupp.single α (MvPolynomial.monomial e 1)) =
      oppositeReadout D B N d m u v (Finsupp.single α (MvPolynomial.monomial e 1)) := by
  have h := word_bpz D hu B hc hp α (occurrences D e) m u v
  simp only [wordPolynomial, occurrences_product, occurrences_weight, hd] at h
  simp only [oppositeReadout, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, rightReadout, smul_eq_mul]
  change B (((Y D (Finsupp.single α (MvPolynomial.monomial e 1)))[[m]]) u) v = _
  rw [h]
  change paritySign d * _ = paritySign d * _
  congr 1
  change (∑ l ∈ Finset.range (e.weight (sourceWeight D) + 1), _) =
    ∑ l ∈ Finset.range N, _
  apply Finset.sum_subset (Finset.range_mono hN)
  intro l hl hnot
  have hlow : e.weight (sourceWeight D) + 1 ≤ l := by
    simpa only [Finset.mem_range, not_lt] using hnot
  have hk := Module.End.pow_map_zero_of_le hlow
    (actual_sugawara_one_monomial_bound D hu α e (1 : ℂ))
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, rightReadout, hk,
    map_zero, mul_zero]

/-- The existing original-carrier nilpotence cutoff, including the zero source. -/
def sourceBound (D : LatticeData) (a : Carrier D) : ℕ :=
  a.support.sup (fun α => MvPolynomial.weightedTotalDegree (sourceWeight D) (a α)) + 1

/-- Conditional BPZ for every actual homogeneous source. The two transpose
suppliers are the signed original current and charged-primary laws. Word charge
covariance, occurrence permutation and the finite L1 regrouping are derived. -/
theorem actual_homogeneous_source_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hcurrent : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hprimary : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (a : Carrier D) (d : ℤ) (ha : a ∈ grade D d)
    (m : ℤ) (u v : Carrier D) :
    B (((Y D a)[[m]]) u) v = paritySign d *
      ∑ l ∈ Finset.range (sourceBound D a), (l.factorial : ℂ)⁻¹ *
        B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l) a))[[
          2*d-l-m-2]]) v) := by
  classical
  let F := rightReadout D B.flip m v u
  let G := oppositeReadout D B (sourceBound D a) d m u v
  suffices h : F a = G a by
    simpa only [F, G, oppositeReadout, rightReadout, LinearMap.smul_apply,
      LinearMap.sum_apply, LinearMap.comp_apply, smul_eq_mul,
      LinearMap.BilinForm.flip_apply] using h
  have singles : (∑ α ∈ a.support, Finsupp.single α (a α)) = a := Finsupp.sum_single a
  rw [← singles, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have expansion := (a α).as_sum
  rw [expansion, Finsupp.single_finsetSum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : chargeEnergy D α + (e.weight (sourceWeight D) : ℤ) = d := by
    by_contra hne
    have hz := (mem_grade_iff D d a).mp ha (α,e) hne
    exact (MvPolynomial.mem_support_iff.mp he) hz
  have hN : e.weight (sourceWeight D) + 1 ≤ sourceBound D a := by
    have h₁ := MvPolynomial.le_weightedTotalDegree (sourceWeight D) he
    have h₂ := Finset.le_sup (f := fun α =>
      MvPolynomial.weightedTotalDegree (sourceWeight D) (a α)) hα
    unfold sourceBound
    omega
  have hbase := basis_bpz_bound D hu B hcurrent hprimary α e (sourceBound D a)
    d m hd hN u v
  have hm : MvPolynomial.monomial e ((a α).coeff e) =
      (a α).coeff e • MvPolynomial.monomial e (1 : ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [hm, ← Finsupp.smul_single, map_smul, map_smul]
  exact congrArg (fun z : ℂ => (a α).coeff e * z) hbase

private theorem projection_bound (D : LatticeData) (a : Carrier D) (d : ℤ) :
    sourceBound D (gradeProjection D d a) ≤ sourceBound D a := by
  classical
  apply Nat.add_le_add_right _ 1
  apply Finset.sup_le
  intro α hα
  have hs : (gradeProjection D d a α).support ⊆ (a α).support := by
    intro e he
    have h := gradeProjection_coeff D d a (α,e)
    change (gradeProjection D d a α).coeff e =
      (if energy D (α,e) = d then (a α).coeff e else 0) at h
    have hn := MvPolynomial.mem_support_iff.mp he
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [h, hz] at hn
    split_ifs at hn <;> exact hn rfl
  have hdeg : MvPolynomial.weightedTotalDegree (sourceWeight D) (gradeProjection D d a α) ≤
      MvPolynomial.weightedTotalDegree (sourceWeight D) (a α) := Finset.sup_mono hs
  apply hdeg.trans
  by_cases hz : a α = 0
  · simp [hz]
  · exact Finset.le_sup (f := fun α =>
      MvPolynomial.weightedTotalDegree (sourceWeight D) (a α))
        (Finsupp.mem_support_iff.mpr hz)

/-- Full finite linear extension using the actual integer grade projections.
Every original source is covered by its finite energy support. The cutoff in
all summands is the actual original bound of the whole source. -/
theorem actual_source_transpose (D : LatticeData) (hu : IsUnit D.G.det)
    (B : LinearMap.BilinForm ℂ (Carrier D))
    (hcurrent : ∀ i : Fin D.rank, ∀ k u v,
      B (neutralMode D i k u) v = -B u (neutralMode D i (-k) v))
    (hprimary : ∀ (α : Charge D) t u v, B (((actualField D α)[[t]]) u) v =
      paritySign (chargeEnergy D α) *
        B u (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) v))
    (a : Carrier D) (m : ℤ) (u v : Carrier D) :
    B (((Y D a)[[m]]) u) v =
      ∑ d ∈ stateEnergies D a, paritySign d *
        ∑ l ∈ Finset.range (sourceBound D a), (l.factorial : ℂ)⁻¹ *
          B u (((Y D ((sugawaraMode D (gramComplex D)⁻¹ 1 ^ l)
            (gradeProjection D d a)))[[2*d-l-m-2]]) v) := by
  classical
  change rightReadout D B.flip m v u a = _
  conv_lhs => rw [← sum_gradeProjections D a, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change B (((Y D (gradeProjection D d a))[[m]]) u) v = _
  rw [actual_homogeneous_source_transpose D hu B hcurrent hprimary
    (gradeProjection D d a) d (gradeProjection_mem D d a)]
  congr 1
  apply Finset.sum_subset (Finset.range_mono (projection_bound D a d))
  intro l hl hnot
  have hlow : sourceBound D (gradeProjection D d a) ≤ l := by
    simpa only [Finset.mem_range, not_lt] using hnot
  have hk := Module.End.pow_map_zero_of_le hlow
    (actual_sugawara_one_bound D hu (gradeProjection D d a))
  simp only [hk, map_zero, mul_zero]

end D5.S3.VertexAlgebra.SourceBPZ
