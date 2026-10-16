/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePeriodicArithmetic
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePeriodicArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One original-entry integer denominator for all actual finite stochastic periodic limits. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteAllStateLimits
import D5.S3.Arith.AbsoluteValues.Heights.Hadamard

open Finset Matrix Filter Topology
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic
open FiniteClosedClasses FiniteGenuinePeriods FiniteClosedClassLimits
open FiniteEntranceDecomposition FiniteAllStateLimits
noncomputable section
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]
local instance (P : Matrix X X ℝ) : DecidablePred (Recurrent P) := Classical.decPred _

private theorem det_bound {S : Type*} [Fintype S] [DecidableEq S]
    (A : Matrix S S ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ x, ∑ y, |A x y| ≤ b) : |A.det| ≤ b ^ Fintype.card S := by
  classical
  let e := Fintype.equivFin S
  let B : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) ℝ :=
    A.submatrix e.symm e.symm
  have hd : B.det = A.det := Matrix.det_submatrix_equiv_self e.symm A
  have hrow (x) : ∑ y, |B x y| ≤ b := by
    simpa only [B, Matrix.submatrix_apply] using
      (Fintype.sum_equiv e.symm (fun y => |B x y|) (fun y => |A (e.symm x) y|)
        (fun _ => rfl)).trans_le (hA (e.symm x))
  have hs (x) : B.row x ⬝ᵥ B.row x ≤ b^2 := by
    have hsum : ∑ y, |B x y|^2 ≤ (∑ y, |B x y|)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun y _ => abs_nonneg (B x y))
    have hsq := mul_self_le_mul_self (sum_nonneg (fun y _ => abs_nonneg (B x y))) (hrow x)
    simpa [dotProduct, Matrix.row, sq_abs, pow_two] using hsum.trans (by simpa [pow_two] using hsq)
  have hh := Matrix.det_mul_transpose_self_le_prod B
  rw [Matrix.det_mul, Matrix.det_transpose, hd] at hh
  have hp : (∏ x, B.row x ⬝ᵥ B.row x) ≤ (b ^ Fintype.card S)^2 := by
    calc
      _ ≤ ∏ _x : Fin (Fintype.card S), b^2 :=
        Finset.prod_le_prod₀
          (fun x _ => by
            simp only [dotProduct, Matrix.row]
            exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _))
          (fun x _ => hs x)
      _ = _ := by simp [← pow_mul, Nat.mul_comm]
  have hh' : |A.det|^2 ≤ (b ^ Fintype.card S)^2 := by
    simpa [sq_abs, pow_two] using hh.trans hp
  nlinarith [abs_nonneg A.det, pow_nonneg hb (Fintype.card S)]

private theorem integer_solution {S : Type*} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℤ) (v : S → ℝ) (b : S → ℤ)
    (hv : (M.map (fun z => (z : ℝ))) *ᵥ v = fun x => (b x : ℝ)) :
    ∀ x, ∃ z : ℤ, (M.det : ℝ) * v x = z := by
  have h := congrArg (fun w => (M.map (fun z => (z : ℝ))).adjugate *ᵥ w) hv
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul] at h
  have hm : (M.map (fun z => (z : ℝ))).adjugate = M.adjugate.map (fun z => (z : ℝ)) :=
    (Int.castRingHom ℝ).map_adjugate M |>.symm
  rw [hm, ← Int.cast_det] at h
  intro x
  refine ⟨(M.adjugate *ᵥ b) x, ?_⟩
  have hx := congrFun h x
  simpa [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply, Int.cast_sum,
    Int.cast_mul] using hx

private theorem natAbs_solution {S : Type*} [Fintype S] [DecidableEq S]
    (M : Matrix S S ℤ) (v : S → ℝ) (b : S → ℤ)
    (hv : (M.map (fun z => (z : ℝ))) *ᵥ v = fun x => (b x : ℝ)) :
    ∀ x, ∃ z : ℤ, (M.det.natAbs : ℝ) * v x = z := by
  intro x
  obtain ⟨z, hz⟩ := integer_solution M v b hv x
  by_cases h : 0 ≤ M.det
  · refine ⟨z, ?_⟩
    simpa [Int.natCast_natAbs, abs_of_nonneg h] using hz
  · refine ⟨-z, ?_⟩
    have hle : M.det ≤ 0 := le_of_not_ge h
    have he : (M.det.natAbs : ℝ) = -(M.det : ℝ) := by
      change ((M.det.natAbs : ℤ) : ℝ) = _
      rw [Int.natCast_natAbs, abs_of_nonpos hle, Int.cast_neg]
    rw [he, Int.cast_neg, neg_mul, hz]

private theorem signed_stationary_zero {P : Matrix X X ℝ} {C : ClosedClass P}
    {K : ClassPeriods P C} (H : ClassLimit K) (v : C.val → ℝ)
    (hv : v ᵥ* restriction P C.val = v) (hs : ∑ x, v x = 0) : v = 0 := by
  classical
  let t : ℝ := 1 + ∑ x, |v x| / H.stationaryRow x
  have hnon (x) : 0 ≤ |v x| / H.stationaryRow x := div_nonneg (abs_nonneg _) (H.positive x).le
  have ht : 0 < t := by
    have hh : 0 ≤ ∑ x, |v x| / H.stationaryRow x := sum_nonneg (fun x _ => hnon x)
    change 0 < 1 + ∑ x, |v x| / H.stationaryRow x
    linarith
  have hbound (x) : |v x| / H.stationaryRow x ≤ t := by
    exact (single_le_sum (fun y _ => hnon y) (mem_univ x)).trans (by dsimp [t]; linarith)
  have hpos (x) : 0 ≤ H.stationaryRow x + v x / t := by
    have hh := (div_le_iff₀ (H.positive x)).mp (hbound x)
    have ha := neg_abs_le (v x)
    have hh2 : -(H.stationaryRow x) ≤ v x / t :=
      (le_div_iff₀ ht).mpr (by nlinarith)
    linarith
  have hnorm : ∑ x, (H.stationaryRow x + v x / t) = 1 := by
    rw [sum_add_distrib, ← sum_div, hs, zero_div, add_zero, H.normalized]
  have hstat : (fun x => H.stationaryRow x + v x / t) ᵥ* restriction P C.val =
      (fun x => H.stationaryRow x + v x / t) := by
    ext y
    change (∑ x, (H.stationaryRow x + v x / t) * restriction P C.val x y) = _
    simp_rw [add_mul, div_mul_eq_mul_div]
    rw [sum_add_distrib, ← sum_div]
    change (H.stationaryRow ᵥ* restriction P C.val) y +
      (v ᵥ* restriction P C.val) y / t = _
    rw [H.stationary, hv]
  have he := H.unique _ hpos hnorm hstat
  ext x
  have hx := congrFun he x
  change H.stationaryRow x + v x / t = H.stationaryRow x at hx
  have : v x / t = 0 := by linarith
  exact (div_eq_zero_iff).mp this |>.resolve_right (ne_of_gt ht)

/-- The normalized original-entry stationary system. -/
private def stationaryIntMatrix (P : Matrix X X ℝ) (E : Matrix X X ℤ) (L : ℕ)
    (C : ClosedClass P) (r : C.val) : Matrix C.val C.val ℤ :=
  fun i j => if i = r then 1 else (if i = j then (L : ℤ) else 0) - E j.val i.val

/-- The original-entry system on transient states and genuine mathematical phases. -/
private def transientIntMatrix (P : Matrix X X ℝ) (E : Matrix X X ℤ) (L : ℕ)
    {C : ClosedClass P} (K : ClassPeriods P C) :
    Matrix (Transient P × ZMod (period (restriction P C.val) K.base))
      (Transient P × ZMod (period (restriction P C.val) K.base)) ℤ :=
  fun a b => (if a = b then (L : ℤ) else 0) -
    if a.2+1 = b.2 then E a.1.val b.1.val else 0

private def transientDenominator (P : Matrix X X ℝ) (E : Matrix X X ℤ) (L : ℕ)
    {C : ClosedClass P} (K : ClassPeriods P C) : ℕ :=
  letI : NeZero (period (restriction P C.val) K.base) := ⟨ne_of_gt K.positive⟩
  (transientIntMatrix P E L K).det.natAbs

private theorem class_denominator {P : Matrix X X ℝ} (hP : P ∈ rowStochastic ℝ X)
    (A : AllStateLimits P) (L N : ℕ) (hL : 0 < L) (hN : Fintype.card X ≤ N)
    (B : Matrix X X ℤ) (hB : ∀ x y, (B x y : ℝ) = (L : ℝ) * P x y)
    (C : ClosedClass P) :
    let b := (stationaryIntMatrix P B L C (A.periods C).base).det.natAbs
    0 < b ∧ b ≤ ((N+1)*L)^N ∧
      ∀ y : C.val, ∃ z : ℤ, (b : ℝ) * (A.classes C).stationaryRow y = z := by
  classical
  let r := (A.periods C).base
  let R := restriction P C.val
  let M := stationaryIntMatrix P B L C r
  let MR := M.map (fun z => (z : ℝ))
  have hm (i j) : MR i j = if i = r then 1 else
      (L : ℝ) * ((if i = j then 1 else 0) - R j i) := by
    dsimp [MR, M, stationaryIntMatrix, Matrix.map]
    split_ifs <;> simp_all [hB, R, restriction] <;> ring
  have hLc : (L : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hL
  have hs := (actual_structure P hP).class_stochastic C
  have hrow (v : C.val → ℝ) (i) : (MR *ᵥ v) i =
      if i = r then ∑ j, v j else (L : ℝ) * (v i - (v ᵥ* R) i) := by
    by_cases hi : i = r
    · simp only [Matrix.mulVec, dotProduct, hm, if_pos hi, one_mul]
    · simp only [Matrix.mulVec, dotProduct, hm, if_neg hi, sub_mul, mul_assoc]
      rw [← mul_sum, sum_sub_distrib]
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', sum_ite_eq, mem_univ, if_true]
      simp only [Matrix.vecMul, dotProduct, mul_comm]
  have hzero : ∀ v : C.val → ℝ, MR *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hsum : ∑ j, v j = 0 := by
      simpa only [hrow, ite_true, Pi.zero_apply] using congrFun hv r
    have hother (i) (hi : i ≠ r) : v i - (v ᵥ* R) i = 0 := by
      have he := congrFun hv i
      rw [hrow, if_neg hi] at he
      exact (mul_eq_zero.mp he).resolve_left hLc
    have ht : ∑ i, (v i - (v ᵥ* R) i) = 0 := by
      rw [sum_sub_distrib]
      have htotal : ∑ i, (v ᵥ* R) i = ∑ j, v j := by
        simp only [Matrix.vecMul, dotProduct]
        rw [sum_comm]
        have hr (j) : ∑ i, R j i = 1 := sum_row_of_mem_rowStochastic hs j
        simp_rw [← mul_sum, hr, mul_one]
      rw [htotal, sub_self]
    have hr : v r - (v ᵥ* R) r = 0 := by
      rw [sum_eq_single r] at ht
      · exact ht
      · intro i _ hi
        exact hother i hi
      · simp
    have hstat : v ᵥ* R = v := by
      ext i
      by_cases hi : i = r
      · subst i; linarith
      · linarith [hother i hi]
    exact signed_stationary_zero (A.classes C) v hstat hsum
  have hdet : MR.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    exact hv (hzero v he)
  have hMi : M.det ≠ 0 := by
    intro he
    apply hdet
    rw [← Int.cast_det, he, Int.cast_zero]
  have heq : MR *ᵥ (A.classes C).stationaryRow =
      fun i => ((if i = r then 1 else 0 : ℤ) : ℝ) := by
    ext i
    rw [hrow]
    split_ifs
    · simpa only [Int.cast_one] using (A.classes C).normalized
    · simp only [R, (A.classes C).stationary, sub_self, mul_zero, Int.cast_zero]
  have hc : Fintype.card C.val ≤ N :=
    ((actual_structure P hP).class_card C).2.trans hN
  have hLP : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hentry (i j) : |MR i j| ≤ (L : ℝ) := by
    rw [hm]
    split_ifs with hi hij
    · simpa using hLP
    · have hn := hs.1 j i
      have hp : R j i ≤ 1 := by
        rw [← sum_row_of_mem_rowStochastic hs j]
        exact single_le_sum (fun k _ => hs.1 j k) (mem_univ i)
      apply abs_le.mpr
      constructor <;> nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    · rw [zero_sub, mul_neg, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg L),
        abs_of_nonneg (hs.1 j i)]
      apply mul_le_of_le_one_right (Nat.cast_nonneg L)
      rw [← sum_row_of_mem_rowStochastic hs j]
      exact single_le_sum (fun k _ => hs.1 j k) (mem_univ i)
  have hbnd : |MR.det| ≤ (((N+1)*L : ℕ) : ℝ) ^ N := by
    calc
      _ ≤ (((N+1)*L : ℕ) : ℝ) ^ Fintype.card C.val :=
        det_bound MR _ (Nat.cast_nonneg _) (fun i => by
          calc
            _ ≤ ∑ _j : C.val, (L : ℝ) := sum_le_sum (fun j _ => hentry i j)
            _ = (Fintype.card C.val : ℝ) * L := by simp
            _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right L (hc.trans (Nat.le_succ N)))
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (Nat.mul_pos (Nat.succ_pos N) hL)) hc
  refine ⟨Int.natAbs_pos.mpr hMi, ?_, natAbs_solution M _ _ heq⟩
  have habs : (M.det.natAbs : ℝ) = |MR.det| := by
    change ((M.det.natAbs : ℤ) : ℝ) = |MR.det|
    rw [Int.natCast_natAbs, Int.cast_abs, Int.cast_det]
  exact_mod_cast (habs ▸ hbnd)

private def phaseLift {S : Type*} (Q : Matrix S S ℝ) (p : ℕ) :
    Matrix (S × ZMod p) (S × ZMod p) ℝ :=
  fun a b => if a.2 + 1 = b.2 then Q a.1 b.1 else 0

private theorem phaseLift_pow {S : Type*} [Fintype S] [DecidableEq S]
    (Q : Matrix S S ℝ) (p : ℕ) [NeZero p] (n : ℕ) (a b : S × ZMod p) :
    (phaseLift Q p ^ n) a b = if a.2 + (n : ZMod p) = b.2 then (Q^n) a.1 b.1 else 0 := by
  classical
  induction n generalizing a b with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, add_zero, Matrix.one_apply]
    by_cases h : a.2 = b.2
    · rw [if_pos h]
      by_cases hs : a.1 = b.1
      · simp [Prod.ext hs h, hs]
      · simp [show a ≠ b from fun he => hs (congrArg Prod.fst he), hs]
    · simp [h, show a ≠ b from fun he => h (congrArg Prod.snd he)]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [ih, phaseLift]
    simp only [ite_mul, zero_mul, sum_ite_eq', sum_ite_eq, mem_univ, if_true]
    simp only [mul_ite, mul_zero, ← Finset.sum_ite_irrel]
    rw [pow_succ, Matrix.mul_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc, Finset.sum_ite_irrel, Finset.sum_const_zero]

private theorem phaseLift_substochastic {S : Type*} [Fintype S] [DecidableEq S]
    (Q : Matrix S S ℝ) (p : ℕ) [NeZero p]
    (hQ : SubstochasticEscape.IsSubstochastic Q) :
    SubstochasticEscape.IsSubstochastic (phaseLift Q p) := by
  classical
  constructor
  · intro a b
    dsimp only [phaseLift]
    split_ifs
    · exact hQ.nonneg _ _
    · exact le_rfl
  · intro a
    simpa [phaseLift, Fintype.sum_prod_type] using hQ.row_le a.1

private theorem phaseLift_rows {S : Type*} [Fintype S] [DecidableEq S]
    (Q : Matrix S S ℝ) (p : ℕ) [NeZero p] (n : ℕ) (a : S × ZMod p) :
    SubstochasticEscape.rowSum (phaseLift Q p) n a =
      SubstochasticEscape.rowSum Q n a.1 := by
  classical
  simp [SubstochasticEscape.rowSum, phaseLift_pow, Fintype.sum_prod_type]

private theorem entrance_succ {P : Matrix X X ℝ} (C : ClosedClass P)
    (n : ℕ) (x : Transient P) (z : C.val) :
    entrance P C (n+1) x z = ∑ v : Transient P, P x.val v.val * entrance P C n v z := by
  simp only [entrance, pow_succ', Matrix.mul_apply, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  change P x.val v.val * (transientMatrix P ^ n) v w * P w.val z.val = _
  ring

private theorem psi_step {P : Matrix X X ℝ} {C : ClosedClass P}
    (H : EntranceLaw P) (K : ClassPeriods P C) (x : Transient P)
    (j : ZMod (period (restriction P C.val) K.base)) :
    psiTransient K x j =
      (∑ z : C.val, if K.phase z - 1 = j then P x.val z.val else 0) +
      ∑ v : Transient P, P x.val v.val * psiTransient K v (j+1) := by
  classical
  let f (x : Transient P) (j : ZMod (period (restriction P C.val) K.base)) (z : C.val)
      (n : ℕ) : ℝ :=
    if K.phase z - (n+1 : ℕ) = j then entrance P C n x z else 0
  have he (z : C.val) (n : ℕ) : f x j z (n+1) =
      ∑ v : Transient P, P x.val v.val * f v (j+1) z n := by
    have hi : K.phase z - (n+1+1 : ℕ) = j ↔ K.phase z - (n+1 : ℕ) = j+1 := by
      push_cast
      constructor <;> intro h <;> linear_combination h
    dsimp only [f]
    simp only [hi, entrance_succ]
    split_ifs <;> simp [*]
  have hzero (z : C.val) : f x j z 0 =
      if K.phase z - 1 = j then P x.val z.val else 0 := by
    simp only [f, entrance, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      sum_ite_eq, sum_ite_eq', mem_univ, ite_true, zero_add, Nat.cast_one]
  have hts (z : C.val) : (∑' n, f x j z n) = f x j z 0 +
      ∑ v : Transient P, P x.val v.val * ∑' n, f v (j+1) z n := by
    have hs : Summable (f x j z) := H.phase_summable C K x z j
    rw [hs.tsum_eq_zero_add]
    simp_rw [he]
    have hv (v : Transient P) : Summable (fun n => P x.val v.val * f v (j+1) z n) :=
      (show Summable (f v (j+1) z) from H.phase_summable C K v z (j+1)).mul_left _
    rw [Summable.tsum_finsetSum (fun v _ => hv v)]
    simp_rw [tsum_mul_left]
  change (∑ z : C.val, ∑' n, f x j z n) = _
  simp_rw [hts, hzero]
  rw [sum_add_distrib, sum_comm]
  congr 1
  apply sum_congr rfl
  intro v _
  rw [← mul_sum]
  rfl

private theorem transient_denominator {P : Matrix X X ℝ} (hP : P ∈ rowStochastic ℝ X)
    (A : AllStateLimits P) (L N : ℕ) (hL : 0 < L) (hN : Fintype.card X ≤ N)
    (B : Matrix X X ℤ) (hB : ∀ x y, (B x y : ℝ) = (L : ℝ) * P x y)
    (C : ClosedClass P) :
    let a := transientDenominator P B L (A.periods C)
    0 < a ∧ a ≤ (2*L)^(N^2) ∧
      ∀ (x : Transient P) (j : ZMod (period (restriction P C.val) (A.periods C).base)),
        ∃ z : ℤ, (a : ℝ) * psiTransient (A.periods C) x j = z := by
  classical
  let K := A.periods C
  let p := period (restriction P C.val) K.base
  let : NeZero p := ⟨ne_of_gt K.positive⟩
  let S := Transient P × ZMod p
  let Q := phaseLift (transientMatrix P) p
  let M : Matrix S S ℤ := transientIntMatrix P B L K
  let MR := M.map (fun z => (z : ℝ))
  let f : S → ℝ := fun a => psiTransient K a.1 a.2
  let rhs : S → ℤ := fun a =>
    ∑ z : C.val, if K.phase z - 1 = a.2 then B a.1.val z.val else 0
  have hm : MR = (L : ℝ) • (1 - Q) := by
    ext a b
    simp only [MR, M, transientIntMatrix, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, Matrix.one_apply, Q, phaseLift]
    split_ifs <;> simp [hB, transientMatrix, Matrix.submatrix_apply] <;> ring
  have hf (a : S) : (Q *ᵥ f) a =
      ∑ v : Transient P, P a.1.val v.val * psiTransient K v (a.2+1) := by
    simp [Matrix.mulVec, dotProduct, Q, phaseLift, f, Fintype.sum_prod_type,
      ite_mul, transientMatrix, Matrix.submatrix_apply]
  have hb (a : S) : (rhs a : ℝ) = (L : ℝ) *
      ∑ z : C.val, if K.phase z - 1 = a.2 then P a.1.val z.val else 0 := by
    simp only [rhs, Int.cast_sum, Int.cast_ite, Int.cast_zero, hB, mul_sum]
    apply sum_congr rfl
    intro z _
    split_ifs <;> simp
  have heq : MR *ᵥ f = fun a => (rhs a : ℝ) := by
    ext a
    rw [hm, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    change (L : ℝ) * (f a - (Q *ᵥ f) a) = _
    rw [hf, hb]
    have hp := psi_step A.entranceLaw K a.1 a.2
    dsimp only [f]
    linear_combination (L : ℝ) * hp
  have hQ := phaseLift_substochastic (transientMatrix P) p (actual_structure P hP).substochastic
  obtain ⟨h, c, hh, hc, hrow⟩ := (actual_structure P hP).escape
  have hdetQ : (1-Q).det ≠ 0 := hQ.det_one_sub_ne_zero hh hc (fun a => by
    simpa only [Q, phaseLift_rows] using hrow a.1)
  have hdet : MR.det ≠ 0 := by
    rw [hm, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast ne_of_gt hL)) hdetQ
  have hMi : M.det ≠ 0 := by
    intro he
    apply hdet
    rw [← Int.cast_det, he, Int.cast_zero]
  have hLP : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hMR (a b : S) : |MR a b| ≤
      (L : ℝ) * (1 : Matrix S S ℝ) a b + (L : ℝ) * Q a b := by
    rw [hm]
    change |(L : ℝ) * ((1 : Matrix S S ℝ) a b - Q a b)| ≤ _
    rw [mul_sub]
    calc
      _ ≤ |(L : ℝ) * (1 : Matrix S S ℝ) a b| + |(L : ℝ) * Q a b| := abs_sub _ _
      _ = _ := by
        rw [abs_of_nonneg (mul_nonneg hLP (by simp only [Matrix.one_apply]; positivity)),
          abs_of_nonneg (mul_nonneg hLP (hQ.nonneg a b))]
  have hbound (a : S) : ∑ b, |MR a b| ≤ (2*L : ℕ) := by
    calc
      _ ≤ ∑ b, ((L : ℝ) * (1 : Matrix S S ℝ) a b + (L : ℝ) * Q a b) :=
        sum_le_sum (fun b _ => hMR a b)
      _ = (L : ℝ) + (L : ℝ) * ∑ b, Q a b := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        have hone : (∑ b : S, (1 : Matrix S S ℝ) a b) = 1 :=
          sum_row_of_mem_rowStochastic ((rowStochastic ℝ S).one_mem) a
        rw [hone, mul_one]
      _ ≤ _ := by have hr := hQ.row_le a; push_cast; nlinarith
  have hcard : Fintype.card S ≤ N^2 := by
    have ht : Fintype.card (Transient P) ≤ N :=
      (Fintype.card_subtype_le _).trans hN
    have hp : p ≤ N := K.bound.trans (((actual_structure P hP).class_card C).2.trans hN)
    simpa only [S, Fintype.card_prod, ZMod.card, pow_two] using Nat.mul_le_mul ht hp
  have hbnd : |MR.det| ≤ ((2*L : ℕ) : ℝ)^(N^2) :=
    (det_bound MR _ (Nat.cast_nonneg _) hbound).trans
      (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2*L)) hcard)
  have habs : (M.det.natAbs : ℝ) = |MR.det| := by
    change ((M.det.natAbs : ℤ) : ℝ) = |MR.det|
    rw [Int.natCast_natAbs, Int.cast_abs, Int.cast_det]
  refine ⟨Int.natAbs_pos.mpr hMi, by exact_mod_cast (habs ▸ hbnd), ?_⟩
  intro x j
  exact natAbs_solution M f rhs heq (x,j)

private theorem denominator_for {P : Matrix X X ℝ} (hP : P ∈ rowStochastic ℝ X)
    (A : AllStateLimits P) (L N : ℕ) (hL : 0 < L) (hN : Fintype.card X ≤ N)
    (B : Matrix X X ℤ) (hB : ∀ x y, (B x y : ℝ) = (L : ℝ) * P x y) :
    ∃ D : ℕ, 0 < D ∧ D ≤ (2*L)^(N^3) * ((N+1)*L)^(N^2) ∧
      (IsEmpty X → D = 1) ∧
      ∀ (i : ℕ) (x y : X), ∃ z : ℤ,
        (D : ℝ) * periodicEntry A.periods A.classes i x y = z := by
  classical
  let a (C : ClosedClass P) := transientDenominator P B L (A.periods C)
  let b (C : ClosedClass P) := (stationaryIntMatrix P B L C (A.periods C).base).det.natAbs
  have ha (C) : 0 < a C ∧ a C ≤ (2*L)^(N^2) ∧
      ∀ x j, ∃ z : ℤ, (a C : ℝ) * psiTransient (A.periods C) x j = z :=
    transient_denominator hP A L N hL hN B hB C
  have hb (C) : 0 < b C ∧ b C ≤ ((N+1)*L)^N ∧
      ∀ y, ∃ z : ℤ, (b C : ℝ) * (A.classes C).stationaryRow y = z :=
    class_denominator hP A L N hL hN B hB C
  let D : ℕ := ∏ C : ClosedClass P, a C * b C
  have hpos : 0 < D := prod_pos (fun C _ => Nat.mul_pos (ha C).1 (hb C).1)
  have hcount := (actual_structure P hP).class_count.trans hN
  have hbound : D ≤ (2*L)^(N^3) * ((N+1)*L)^(N^2) := by
    calc
      _ ≤ ∏ _C : ClosedClass P, (2*L)^(N^2) * ((N+1)*L)^N :=
        prod_le_prod' (fun C _ => Nat.mul_le_mul (ha C).2.1 (hb C).2.1)
      _ = (2*L)^(N^2 * Fintype.card (ClosedClass P)) *
          ((N+1)*L)^(N * Fintype.card (ClosedClass P)) := by
        simp [mul_pow, ← pow_mul]
      _ ≤ _ := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.mul_le_mul_left (N^2) hcount]))
        (Nat.pow_le_pow_right (Nat.mul_pos (Nat.succ_pos N) hL)
          (by nlinarith [Nat.mul_le_mul_left N hcount]))
  refine ⟨D, hpos, hbound, ?_, ?_⟩
  · intro hx
    let := (actual_structure P hP).empty_ambient hx
    simp [D]
  · intro i x y
    by_cases hy : Recurrent P y
    · let C := hy.choose
      let yy : C.val := ⟨y, hy.choose_spec⟩
      let p := period (restriction P C.val) (A.periods C).base
      have hdiv : a C * b C ∣ D := dvd_prod_of_mem (fun C => a C * b C) (mem_univ C)
      obtain ⟨q, hq⟩ := hdiv
      obtain ⟨zp, hzp⟩ := (hb C).2.2 yy
      simp only [periodicEntry, dif_pos hy]
      change ∃ z : ℤ, (D : ℝ) *
        (if hx : x ∈ C.val then
          if (A.periods C).phase ⟨x,hx⟩ + (i : ZMod p) = (A.periods C).phase yy
          then (p : ℝ) * (A.classes C).stationaryRow yy else 0
        else if ht : ¬ Recurrent P x then
          (p : ℝ) * (A.classes C).stationaryRow yy *
            psiTransient (A.periods C) ⟨x,ht⟩ ((A.periods C).phase yy - (i : ZMod p))
        else 0) = z
      by_cases hx : x ∈ C.val
      · rw [dif_pos hx]
        split_ifs
        · refine ⟨((a C * q * p : ℕ) : ℤ) * zp, ?_⟩
          rw [hq]
          push_cast
          rw [← hzp]
          ring
        · exact ⟨0, by simp⟩
      · rw [dif_neg hx]
        by_cases ht : ¬ Recurrent P x
        · rw [dif_pos ht]
          obtain ⟨ze, hze⟩ := (ha C).2.2 ⟨x,ht⟩ ((A.periods C).phase yy - (i : ZMod p))
          refine ⟨(q : ℤ) * (p : ℤ) * zp * ze, ?_⟩
          rw [hq]
          push_cast
          rw [← hzp, ← hze]
          ring
        · rw [dif_neg ht]
          exact ⟨0, by simp⟩
    · exact ⟨0, by simp [periodicEntry, hy]⟩

/-- One positive integer constructed from original one-step entries clears every actual
periodic limit, with the PH38.2 bound independent of the subsequence stride and residue. -/
theorem actual_common_denominator (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (N L : ℕ) (hN : Fintype.card X ≤ N) (hL : 0 < L)
    (hclear : ∀ x y, ∃ z : ℤ, (L : ℝ) * P x y = z) :
    ∃ (A : AllStateLimits P) (D : ℕ), 0 < D ∧
      D ≤ (2*L)^(N^3) * ((N+1)*L)^(N^2) ∧ (IsEmpty X → D = 1) ∧
      (∀ (B : AllStateLimits P) (i : ℕ) (x y : X), ∃ z : ℤ,
        (D : ℝ) * periodicEntry B.periods B.classes i x y = z) ∧
      ∀ (B : AllStateLimits P) (d : ℕ), 0 < d →
        (∀ C, period (restriction P C.val) (B.periods C).base ∣ d) →
        ∀ (i : ℕ) (x y : X), ∃ z : ℤ,
          periodicEntry B.periods B.classes i x y = (z : ℝ) / (D : ℝ) ∧
          Tendsto (fun t : ℕ => (P^(d*t+i)) x y) atTop (𝓝 ((z : ℝ) / (D : ℝ))) := by
  classical
  let A := Classical.choice (actual_all_state_limits P hP)
  let E : Matrix X X ℤ := fun x y => (hclear x y).choose
  have hE (x y) : (E x y : ℝ) = (L : ℝ) * P x y := (hclear x y).choose_spec.symm
  obtain ⟨D, hD, hb, hempty, hentries⟩ := denominator_for hP A L N hL hN E hE
  have heq (B : AllStateLimits P) (i : ℕ) (x y : X) :
      periodicEntry A.periods A.classes i x y = periodicEntry B.periods B.classes i x y := by
    let d := ∏ C : ClosedClass P, period (restriction P C.val) (A.periods C).base
    have hd : 0 < d := prod_pos (fun C _ => (A.periods C).positive)
    have ha (C) : period (restriction P C.val) (A.periods C).base ∣ d :=
      dvd_prod_of_mem _ (mem_univ C)
    have hb (C) : period (restriction P C.val) (B.periods C).base ∣ d := by
      rw [(A.periods C).independent (B.periods C).base]
      exact ha C
    exact tendsto_nhds_unique (A.convergence d hd ha i x y) (B.convergence d hd hb i x y)
  have hentriesB (B : AllStateLimits P) (i : ℕ) (x y : X) :
      ∃ z : ℤ, (D : ℝ) * periodicEntry B.periods B.classes i x y = z := by
    rw [← heq B i x y]
    exact hentries i x y
  refine ⟨A, D, hD, hb, hempty, hentriesB, ?_⟩
  intro B d hd hpd i x y
  obtain ⟨z, hz⟩ := hentriesB B i x y
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have he : periodicEntry B.periods B.classes i x y = (z : ℝ) / (D : ℝ) :=
    (eq_div_iff hDr).mpr (by nlinarith [hz])
  refine ⟨z, he, ?_⟩
  rw [← he]
  exact B.convergence d hd hpd i x y

#print axioms actual_common_denominator

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePeriodicArithmetic
