/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitDenominator
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitDenominator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One reachable integer determinant clears the actual fair-tape exit laws. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitExitLaws
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape
import D5.S3.Arith.AbsoluteValues.Heights.Hadamard
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
open FiniteFairBitFirstReturn FiniteFairBitExitLaws

/-- Both fair alternatives count, including coincident successors. -/
def count {X : Type} [DecidableEq X] (i : Instruction X) (x : X) : ℤ :=
  match i with
  | .deterministic a => if x = a then 2 else 0
  | .fair a b => (if x = a then 1 else 0) + (if x = b then 1 else 0)

private theorem count_nonneg {X : Type} [DecidableEq X] (i : Instruction X) (x : X) :
    0 ≤ count i x := by
  cases i <;> simp only [count] <;> split_ifs <;> norm_num

private theorem count_mass {X : Type} [DecidableEq X]
    (d : X → Instruction X) (s x : X) :
    (row d s x).toReal = (count (d s) x : ℝ) / 2 := by
  cases h : d s with
  | deterministic a => simp only [row,h,count,PMF.pure_apply]; split_ifs <;> norm_num
  | fair a b =>
    simp only [row,h,count,row_fair]
    split_ifs <;> norm_num [ENNReal.toReal_add,ENNReal.inv_two_add_inv_two]

private theorem count_total {X : Type} [Fintype X] [DecidableEq X]
    (d : X → Instruction X) (s : X) : ∑ x, (count (d s) x : ℝ) = 2 := by
  have h : (∑ x, row d s x).toReal = 1 := by
    have he : (∑ x, row d s x) = 1 := by
      simpa only [tsum_fintype] using (row d s).tsum_coe
    rw [he,ENNReal.toReal_one]
  rw [ENNReal.toReal_sum (fun x _ => (row d s).apply_ne_top x)] at h
  simp_rw [count_mass] at h
  rw [← Finset.sum_div] at h
  linarith

variable {S O : Type} [Fintype S] [Fintype O]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace O] [MeasurableSingletonClass O]

abbrev U (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) :=
  {s : S // Reachable d E s}

def N (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : Matrix (U d E) (U d E) ℤ :=
  fun s t => count (d s.val) (.inl t.val)
def C (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : Matrix (U d E) O ℤ :=
  fun s o => count (d s.val) (.inr o)
def A (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : Matrix (U d E) (U d E) ℤ :=
  (2 : ℤ) • 1 - N d E
def realT (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : Matrix (U d E) (U d E) ℝ :=
  fun s t => (T d s.val t.val).toReal
def realZ (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : Matrix (U d E) O ℝ :=
  fun s o => (Z d s.val o).toReal

private theorem counts_cast (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) :
    (∀ s t : U d E, realT d E s t = (N d E s t : ℝ) / 2) ∧
    (∀ (s : U d E) (o : O), (R d s.val o).toReal = (C d E s o : ℝ) / 2) := by
  constructor <;> intro s t <;>
    exact count_mass (stopped d) (.inl s.val) _

private theorem trim_sum {K : Type} [AddCommMonoid K]
    (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) (f : S → K)
    (hf : ∀ t, ¬ Reachable d E t → f t = 0) :
    (∑ t : U d E, f t.val) = ∑ t : S, f t := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (Reachable d E) f
  have hz : (∑ t : {t : S // ¬ Reachable d E t}, f t.val) = 0 :=
    Finset.sum_eq_zero fun t _ => hf t.val t.property
  simpa only [hz,add_zero] using h

private theorem power_bridge (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) (n : ℕ) (s t : U d E) :
    (realT d E ^ n) s t = ((T d ^ n) s.val t.val).toReal := by
  obtain ⟨L,hL,hblock,hgeom,hlim,hzero⟩ := reachable_escape d E hE
  have hfin (n : ℕ) (s t : S) : (T d ^ n) s t ≠ ∞ := by
    rw [← (finite_exit_laws d (.inl s)).2.2.2.2.1 s t n]
    exact measure_ne_top _ _
  induction n generalizing s t with
  | zero =>
    by_cases h : s = t
    · subst t; simp [Matrix.one_apply]
    · have hv : s.val ≠ t.val := fun he => h (Subtype.ext he)
      simp [Matrix.one_apply,h,hv]
  | succ n ih =>
    rw [pow_succ,Matrix.mul_apply,pow_succ,Matrix.mul_apply,
      ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (hfin n _ _) (show T d x t.val ≠ ∞ from (row (stopped d) (.inl x)).apply_ne_top _))]
    simp_rw [ENNReal.toReal_mul]
    rw [← trim_sum d E (fun x => ((T d ^ n) s.val x).toReal * (T d x t.val).toReal)
      (fun x hx => by rw [hzero _ _ s.property hx n]; simp)]
    exact Finset.sum_congr rfl fun x _ => by rw [ih]; rfl

private theorem matrix_cast (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) :
    (A d E).map (Int.castRingHom ℝ) = (2 : ℝ) • (1 - realT d E) := by
  ext s t
  have h := (counts_cast d E).1 s t
  simp only [A,Matrix.map_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
    smul_eq_mul,Int.cast_sub,Int.cast_mul]
  push_cast
  split_ifs <;> norm_num at * <;> linarith


private theorem subsum_le {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (g : Y → X) (hg : Function.Injective g) :
    (∑ y, f (g y)) ≤ ∑ x, f x := by
  classical
  rw [← Finset.sum_image (fun x _ y _ h => hg h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x _ _ => hf x)

private theorem counts_row_le (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (s : U d E) : (∑ t, (N d E s t : ℝ)) ≤ 2 := by
  have h := subsum_le (fun x => (count (d s.val) x : ℝ))
    (fun x => by exact_mod_cast count_nonneg (d s.val) x)
    (fun t : U d E => Sum.inl t.val)
    (fun x y h => Subtype.ext (Sum.inl.inj h))
  have ht := count_total (stopped d) (.inl s.val)
  change (∑ x, (count (d s.val) x : ℝ)) = 2 at ht
  simpa only [N,ht] using h

private theorem substochastic (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) :
    SubstochasticEscape.IsSubstochastic (realT d E) where
  nonneg s t := ENNReal.toReal_nonneg
  row_le s := by
    simp_rw [(counts_cast d E).1]
    rw [← Finset.sum_div]
    have h := counts_row_le d E s
    linarith

private theorem row_l1 (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (s : U d E) : ∑ t, |((A d E s t : ℤ) : ℝ)| ≤ 4 := by
  have hbound (t : U d E) : |((A d E s t : ℤ) : ℝ)| ≤
      (if s = t then 2 else 0) + (N d E s t : ℝ) := by
    have hn : 0 ≤ (N d E s t : ℝ) := by exact_mod_cast count_nonneg (d s.val) (.inl t.val)
    simp only [A,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    push_cast
    split_ifs <;> norm_num <;> apply abs_le.mpr <;> constructor <;> linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hbound t)
  rw [Finset.sum_add_distrib] at h
  have hn := counts_row_le d E s
  have hd : (∑ t : U d E, if s = t then (2 : ℝ) else 0) = 2 := by simp
  rw [hd] at h
  linarith

private theorem real_renewal (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) :
    (A d E).map (Int.castRingHom ℝ) * realZ d E = (C d E).map (Int.castRingHom ℝ) := by
  obtain ⟨L,hL,hblock,hgeom,hlim,hzero⟩ := reachable_escape d E hE
  have he (s : U d E) (o : O) :
      realZ d E s o = (R d s.val o).toReal + (realT d E * realZ d E) s o := by
    have h := congrArg ENNReal.toReal (congrFun (congrFun (actual_renewal d) s.val) o)
    have hR : R d s.val o ≠ ∞ := (row (stopped d) (.inl s.val)).apply_ne_top _
    have hp (t : S) : T d s.val t * Z d t o ≠ ∞ :=
      ENNReal.mul_ne_top ((row (stopped d) (.inl s.val)).apply_ne_top _) (measure_ne_top _ _)
    simp only [Matrix.add_apply,Matrix.mul_apply] at h
    rw [ENNReal.toReal_add hR (ENNReal.sum_ne_top.mpr (fun t _ => hp t)),
      ENNReal.toReal_sum (fun t _ => hp t)] at h
    simp_rw [ENNReal.toReal_mul] at h
    rw [← trim_sum d E (fun t => (T d s.val t).toReal * (Z d t o).toReal)
      (fun t ht => by
        have hz : T d s.val t = 0 := by simpa using hzero s.val t s.property ht 1
        rw [hz]
        simp)] at h
    exact h
  rw [matrix_cast,Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul]
  ext s o
  have h := he s o
  have hr := (counts_cast d E).2 s o
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,Matrix.map_apply]
  change 2 * (realZ d E s o - (realT d E * realZ d E) s o) = (C d E s o : ℝ)
  linarith

private theorem det_ne_zero (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) : (A d E).det ≠ 0 := by
  obtain ⟨L,hL,hblock,hgeom,hlim,hzero⟩ := reachable_escape d E hE
  have hc (s : U d E) : SubstochasticEscape.rowSum (realT d E) L s ≤ (1/2 : ℝ) := by
    simp only [SubstochasticEscape.rowSum]
    simp_rw [power_bridge d E hE]
    rw [trim_sum d E (fun t => ((T d ^ L) s.val t).toReal)
      (fun t ht => by rw [hzero _ _ s.property ht]; simp)]
    have hfin (t : S) : (T d ^ L) s.val t ≠ ∞ := by
      rw [← (finite_exit_laws d (.inl s.val)).2.2.2.2.1 s.val t L]
      exact measure_ne_top _ _
    rw [← ENNReal.toReal_sum (fun t _ => hfin t),
      ← (finite_exit_laws d (.inl s.val)).2.2.2.2.2.1 s.val L]
    have h := ENNReal.toReal_mono (by norm_num : (1/2 : ℝ≥0∞) ≠ ∞) (hblock s.val s.property)
    norm_num at h ⊢
    exact h
  have hn := (substochastic d E).det_one_sub_ne_zero hL (by norm_num : (1/2 : ℝ) < 1) hc
  intro hz
  have hm := (Int.castRingHom ℝ).map_det (A d E)
  change ((A d E).det : ℝ) = ((A d E).map (Int.castRingHom ℝ)).det at hm
  rw [hz,Int.cast_zero,matrix_cast,Matrix.det_smul] at hm
  exact hn ((mul_eq_zero.mp hm.symm).resolve_left (pow_ne_zero _ (by norm_num)))

private theorem adjugate_equation (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) :
    ((A d E).det : ℝ) • realZ d E =
      ((A d E).adjugate * C d E).map (Int.castRingHom ℝ) := by
  have h := congrArg (fun M => (A d E).adjugate.map (Int.castRingHom ℝ) * M)
    (real_renewal d E hE)
  rw [← Matrix.map_mul,← Matrix.mul_assoc,← Matrix.map_mul,Matrix.adjugate_mul] at h
  have hm : ((A d E).det • (1 : Matrix (U d E) (U d E) ℤ)).map (Int.castRingHom ℝ) =
      ((A d E).det : ℝ) • (1 : Matrix (U d E) (U d E) ℝ) := by
    ext s t
    simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
    split_ifs <;> simp
  rwa [hm,Matrix.smul_mul,Matrix.one_mul] at h

private theorem determinant_bound (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) :
    (A d E).det.natAbs ≤ 4 ^ Fintype.card (U d E) := by
  let e := Fintype.equivFin (U d E)
  let M : Matrix (Fin (Fintype.card (U d E))) (Fin (Fintype.card (U d E))) ℝ :=
    ((A d E).map (Int.castRingHom ℝ)).submatrix e.symm e.symm
  have hd : M.det = ((A d E).det : ℝ) := by
    rw [Matrix.det_submatrix_equiv_self]
    exact ((Int.castRingHom ℝ).map_det _).symm
  have hl (i : Fin (Fintype.card (U d E))) : ∑ j, |M i j| ≤ 4 := by
    calc
      (∑ j, |M i j|) = ∑ t, |((A d E (e.symm i) t : ℤ) : ℝ)| :=
        Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ ≤ 4 := row_l1 d E (e.symm i)
  have hs (i : Fin (Fintype.card (U d E))) : M.row i ⬝ᵥ M.row i ≤ 16 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset _)) => abs_nonneg (M i j))
    have hl' := hl i
    have hnn : 0 ≤ ∑ j, |M i j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [sq_abs] at h
    change (∑ j, M i j * M i j) ≤ 16
    simp only [← sq]
    nlinarith
  have hH := Matrix.det_mul_transpose_self_le_prod M
  have hp : (∏ i, M.row i ⬝ᵥ M.row i) ≤ (16 : ℝ) ^ Fintype.card (U d E) := by
    calc
      _ ≤ ∏ _i : Fin (Fintype.card (U d E)), (16 : ℝ) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _) (fun i _ => hs i)
      _ = _ := by simp
  rw [Matrix.det_mul,Matrix.det_transpose,hd] at hH
  have hsq : ((A d E).det.natAbs : ℝ)^2 ≤ ((4 : ℝ)^Fintype.card (U d E))^2 := by
    have he : (16 : ℝ)^Fintype.card (U d E) = ((4 : ℝ)^Fintype.card (U d E))^2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have h := hH.trans hp
    rw [he] at h
    norm_num [← Int.cast_pow,Int.natAbs_sq,sq] at *
    exact h
  have hreal : ((A d E).det.natAbs : ℝ) ≤ (4 : ℝ)^Fintype.card (U d E) := by
    nlinarith [show (0 : ℝ) ≤ (4 : ℝ)^Fintype.card (U d E) by positivity,
      show (0 : ℝ) ≤ ((A d E).det.natAbs : ℝ) by positivity]
  exact_mod_cast hreal

/-- The single certificate indexes charged internal states only. -/
def denominator (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O)) : ℕ := (A d E).det.natAbs

def Clears (k : ℕ) (x : ℝ) : Prop := ∃ z : ℕ, (k : ℝ) * x = z

/-- One determinant clears the literal eventual label events for every entrance and reachable state. -/
theorem actual_exit_denominator (d : S → Instruction (S ⊕ O)) (E : Set (S ⊕ O))
    (hE : ∀ a ∈ E, tapeLaw (never d a) = 0) :
    0 < denominator d E ∧ denominator d E ≤ 4 ^ Fintype.card (U d E) ∧
    (∀ (s : U d E) (o : O), Clears (denominator d E) (Z d s.val o).toReal) ∧
    (∀ a ∈ E, ∀ o, Clears (denominator d E) (tapeLaw (exits d a o)).toReal) ∧
    (∀ a ∈ E, ∑ o, tapeLaw (exits d a o) = 1) := by
  have hc (s : U d E) (o : O) : Clears (denominator d E) (Z d s.val o).toReal := by
    let z := ((A d E).adjugate * C d E) s o
    have h := congrFun (congrFun (adjugate_equation d E hE) s) o
    change ((A d E).det : ℝ) * (Z d s.val o).toReal = (z : ℝ) at h
    have ha := congrArg abs h
    rw [abs_mul,abs_of_nonneg ENNReal.toReal_nonneg] at ha
    refine ⟨z.natAbs,?_⟩
    simpa [denominator,Nat.cast_natAbs,Int.cast_abs] using ha
  refine ⟨Int.natAbs_pos.mpr (det_ne_zero d E hE),determinant_bound d E,hc,?_,
    (normalized_reachable_exits d E hE).1⟩
  intro a ha o
  cases a with
  | inl s => exact hc ⟨s,Reachable.entrance s ha⟩ o
  | inr p =>
    rw [exits_exit]
    by_cases hp : p = o
    · simp only [hp,ite_true,ENNReal.toReal_one]
      exact ⟨denominator d E,by simp⟩
    · simp only [hp,ite_false,ENNReal.toReal_zero]
      exact ⟨0,by simp⟩

/-- A complete installation codec pays for the whole shared internal carrier. -/
theorem charged_exit_denominator {p m a B : ℕ} (P : Program p a)
    (micro : Set (Snapshot p m a)) [Fintype micro]
    [MeasurableSpace micro] [MeasurableSingletonClass micro]
    (c : CompleteCodec P micro B) (d : micro → Instruction (micro ⊕ O))
    (E : Set (micro ⊕ O)) (hE : ∀ x ∈ E, tapeLaw (never d x) = 0) :
    0 < denominator d E ∧ denominator d E ≤ 4 ^ (2 ^ B) ∧
    (∀ x ∈ E, ∀ o, Clears (denominator d E) (tapeLaw (exits d x o)).toReal) := by
  have h := actual_exit_denominator d E hE
  have hc := (charged_cardinality c (∅ : Set micro)).1
  have hu : Fintype.card (U d E) ≤ Fintype.card micro := Fintype.card_subtype_le _
  rw [Nat.card_eq_fintype_card] at hc
  exact ⟨h.1,h.2.1.trans (Nat.pow_le_pow_right (by omega) (hu.trans hc)),h.2.2.2.1⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteFairBitDenominator
