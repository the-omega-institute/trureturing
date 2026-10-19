/- GID: D5/S3/StatisticalMechanics/SingleEntryFiniteNetwork
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntryFiniteNetwork
   mirror-E: none(waiver:finite-single-entry-forward-system)
   anchors: []
   utility: none
   digest: Finite Boolean single-entry networks have strictly positive pair association. -/

import D5.S3.StatisticalMechanics.SingleEntryFiveState

/-! # Association in a finite single-entry Boolean network -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Set Filter
namespace D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The rates are independently specified on every actual binding site. -/
structure Rates (I : Type*) where
  a : I → ℝ
  b : I → ℝ
  eta : ℝ
  theta : ℝ
  a_pos : ∀ i, 0 < a i
  b_pos : ∀ i, 0 < b i
  eta_pos : 0 < eta
  theta_pos : 0 < theta

private def src : Option (I × Finset I) → Option (Finset I)
  | none => none
  | some (_, S) => some S
private def dst : Option (I × Finset I) → Option (Finset I)
  | none => some ∅
  | some (i, S) => some (insert i S)
private def up (k : Rates I) : Option (I × Finset I) → ℝ
  | none => Real.sqrt k.theta
  | some (i, S) => if i ∈ S then 0 else Real.sqrt (k.a i)
private def down (k : Rates I) : Option (I × Finset I) → ℝ
  | none => Real.sqrt k.eta
  | some (i, S) => if i ∈ S then 0 else Real.sqrt (k.b i)

/-- The column generator is the sum of the actual two-way transition edges.
Each absent site binds at rate `a i`, each present site unbinds at rate `b i`;
only the empty set communicates with the inhibited state. -/
def generator (k : Rates I) : Matrix (Option (Finset I)) (Option (Finset I)) ℝ := fun x y =>
  ∑ e : Option (I × Finset I), ((if x = dst e then 1 else 0) - (if x = src e then 1 else 0)) *
    ((up k e)^2 * (if y = src e then 1 else 0) -
      (down k e)^2 * (if y = dst e then 1 else 0))

/-- The initial law and the generator anchor every coordinate of a trajectory. -/
def ForwardSolution (k : Rates I) (p : ℝ → Option (Finset I) → ℝ) : Prop :=
  p 0 = Pi.single none 1 ∧ ∀ t, 0 ≤ t → ∀ x,
    HasDerivAt (fun u => p u x) ((generator k *ᵥ p t) x) t

private def incidence (k : Rates I) : Matrix (Option (I × Finset I)) (Option (Finset I)) ℝ := fun e x =>
  up k e * (if x = src e then 1 else 0) - down k e * (if x = dst e then 1 else 0)
private def gram (k : Rates I) : Matrix (Option (Finset I)) (Option (Finset I)) ℝ :=
  (incidence k).transpose * incidence k
private def scale (k : Rates I) : Option (Finset I) → ℝ
  | none => Real.sqrt k.eta * ∏ i, Real.sqrt (k.b i)
  | some S => Real.sqrt k.theta * ∏ i, if i ∈ S then Real.sqrt (k.a i) else Real.sqrt (k.b i)

private theorem scale_pos (k : Rates I) (x : Option (Finset I)) : 0 < scale k x := by
  cases x with
  | none =>
    exact mul_pos (Real.sqrt_pos.mpr k.eta_pos)
      (Finset.prod_pos (fun i _ => Real.sqrt_pos.mpr (k.b_pos i)))
  | some S =>
    apply mul_pos (Real.sqrt_pos.mpr k.theta_pos)
    apply Finset.prod_pos
    intro i _
    split_ifs <;> exact Real.sqrt_pos.mpr (by first | exact k.a_pos i | exact k.b_pos i)

private theorem edge_balance (k : Rates I) (e : Option (I × Finset I)) :
    up k e * scale k (src e) = down k e * scale k (dst e) := by
  cases e with
  | none => simp [up, down, src, dst, scale, mul_assoc, mul_left_comm, mul_comm]
  | some p =>
    rcases p with ⟨i, S⟩
    by_cases hi : i ∈ S
    · simp [up, down, hi]
    · have hprod (T : Finset I) (f : I → ℝ) :
          (∏ j, f j) = f i * ∏ j ∈ Finset.univ.erase i, f j := by
        exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      dsimp [up, down, src, dst, scale]
      simp only [hi, ↓reduceIte]
      rw [hprod S, hprod (insert i S)]
      simp only [hi, ↓reduceIte, Finset.mem_insert_self]
      have he : (∏ j ∈ Finset.univ.erase i,
          if j ∈ S then Real.sqrt (k.a j) else Real.sqrt (k.b j)) =
          ∏ j ∈ Finset.univ.erase i,
          if j ∈ insert i S then Real.sqrt (k.a j) else Real.sqrt (k.b j) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        simp [Finset.mem_insert, hji]
      rw [he]
      ring

private theorem similarity (k : Rates I) (x y : Option (Finset I)) :
    generator k x y * scale k y = -(scale k x * gram k x y) := by
  simp only [generator, gram, Matrix.mul_apply, transpose_apply, incidence,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hb := edge_balance k e
  have hu := congrArg (fun z : ℝ => up k e * z) hb
  have hd := congrArg (fun z : ℝ => down k e * z) hb
  have hn := ne_of_gt (scale_pos k (src e))
  by_cases hloop : src e = dst e
  · have hud : up k e = down k e := by
      apply mul_right_cancel₀ hn
      simpa [← hloop] using hb
    simp [← hloop, hud]
  · by_cases hxs : x = src e <;> by_cases hxd : x = dst e <;>
      by_cases hys : y = src e <;> by_cases hyd : y = dst e <;>
      simp_all <;> nlinarith [
        congrArg (fun z : ℝ => z * up k e) (edge_balance k e),
        congrArg (fun z : ℝ => z * down k e) (edge_balance k e)]

private theorem generator_dual (k : Rates I) (f p : Option (Finset I) → ℝ) :
    (∑ x, f x * (generator k *ᵥ p) x) =
      ∑ e : Option (I × Finset I), (f (dst e) - f (src e)) *
        ((up k e)^2 * p (src e) - (down k e)^2 * p (dst e)) := by
  change (∑ x, f x * ∑ y, (∑ e : Option (I × Finset I),
    ((if x = dst e then 1 else 0) - (if x = src e then 1 else 0)) *
    ((up k e)^2 * (if y = src e then 1 else 0) -
      (down k e)^2 * (if y = dst e then 1 else 0))) * p y) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ e : Option (I × Finset I), ∑ y,
        f x * (((if x = dst e then 1 else 0) - (if x = src e then 1 else 0)) *
          ((up k e)^2 * (if y = src e then 1 else 0) -
            (down k e)^2 * (if y = dst e then 1 else 0)) * p y) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ e : Option (I × Finset I), ∑ x, ∑ y,
        f x * (((if x = dst e then 1 else 0) - (if x = src e then 1 else 0)) *
          ((up k e)^2 * (if y = src e then 1 else 0) -
            (down k e)^2 * (if y = dst e then 1 else 0)) * p y) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [← mul_assoc, ← Finset.mul_sum]
      simp [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul,
        Finset.mul_sum, Finset.sum_mul]
      ring

private theorem spectral_data (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) :
    (∀ t, 0 ≤ t → 0 < k.theta * p t none - k.eta * p t (some ∅)) ∧
    (∃ lam c : Option (Finset I) → ℝ,
      (∀ j, 0 ≤ lam j ∧ 0 ≤ c j) ∧ (∑ j, c j) = 1 ∧
      (∃ j, 0 < lam j * c j) ∧
      ∀ t, 0 ≤ t → p t none = ∑ j, c j * Real.exp (-lam j * t)) ∧
    ∃ L : Option (Finset I) → ℝ,
      (∀ x, Tendsto (fun t => p t x) atTop (nhds (L x))) ∧ generator k *ᵥ L = 0 := by
  let y := fun u i => scale k none / scale k i * p u i
  have hn (i : Option (Finset I)) : scale k i ≠ 0 := ne_of_gt (scale_pos k i)
  have hA : (gram k).PosSemidef := by
    simpa [gram, star_eq_conjTranspose] using posSemidef_conjTranspose_mul_self (incidence k)
  have hy0 : y 0 = Pi.single none 1 := by
    funext i
    dsimp [y]
    rw [hp.1]
    by_cases hi : i = none
    · subst i; simp [hn]
    · simp [Pi.single_apply, hi, Ne.symm hi]
  have hy (u : ℝ) (hu : 0 ≤ u) (i : Option (Finset I)) :
      HasDerivAt (fun x => y x i) (-(gram k *ᵥ y u) i) u := by
    convert (hp.2 u hu i).const_mul (scale k none / scale k i) using 1
    dsimp [y, mulVec, dotProduct]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hs := similarity k i j
    field_simp [hn]
    nlinarith [congrArg (fun z : ℝ => z * p u j) hs]
  have hdiag : 0 < gram k none none := by
    change 0 < ∑ e : Option (I × Finset I), incidence k e none * incidence k e none
    have hh := Finset.single_le_sum (fun e (_ : e ∈ (Finset.univ : Finset (Option (I × Finset I)))) =>
      mul_self_nonneg (incidence k e none)) (Finset.mem_univ (none : Option (I × Finset I)))
    have he : incidence k none none * incidence k none none = k.theta := by
      simp [incidence, up, down, src, dst, Real.sq_sqrt k.theta_pos.le, ← pow_two]
    rw [he] at hh
    exact lt_of_lt_of_le k.theta_pos hh
  obtain ⟨lam, c, hnon, hsum, hmode, hrep, hdecr, l, hlim, hstat, _, _⟩ :=
    SingleEntryFiveState.symmetric_return_data (gram k) hA none hdiag y hy0 hy
  have he : (fun u => y u none) = (fun u => p u none) := by
    funext u; simp [y, hn]
  have hQ (u : ℝ) : (generator k *ᵥ p u) none =
      -k.theta * p u none + k.eta * p u (some ∅) := by
    simp [generator, mulVec, dotProduct, src, dst, up, down,
      Fintype.sum_option, Fintype.sum_prod_type, Finset.mul_sum,
      Real.sq_sqrt k.theta_pos.le, Real.sq_sqrt k.eta_pos.le]
  refine ⟨?_, ⟨lam, c, hnon, hsum, hmode, ?_⟩, ?_⟩
  · intro t ht
    have hd := hdecr t ht
    rw [he, (hp.2 t ht none).deriv, hQ] at hd
    linarith
  · intro t ht
    change (fun u => p u none) t = _
    rw [← he]
    exact hrep t ht
  · let L : Option (Finset I) → ℝ := fun i => scale k i / scale k none * l i
    refine ⟨L, ?_, ?_⟩
    · intro i
      have heq : (fun t => p t i) = (fun t => scale k i / scale k none * y t i) := by
        funext t
        dsimp [y]
        field_simp [hn]
      rw [heq]
      exact (hlim i).const_mul _
    · ext i
      have hz := congrFun hstat i
      change (generator k *ᵥ L) i = 0
      have hid : (generator k *ᵥ L) i =
          -(scale k i / scale k none * (gram k *ᵥ l) i) := by
        dsimp [mulVec, dotProduct, L]
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have hs := similarity k i j
        field_simp [hn]
        nlinarith [congrArg (fun z : ℝ => z * l j) hs]
      rw [hid, hz]
      simp

private theorem sum_insert (i : I) (g : Finset I → ℝ) :
    (∑ S : Finset I, if i ∉ S then g (insert i S) else 0) =
      ∑ S : Finset I, if i ∈ S then g S else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun S _ => insert i S)
  · intro S hS
    simp
  · intro S hS T hT he
    have hiS : i ∉ S := (Finset.mem_filter.mp hS).2
    have hiT : i ∉ T := (Finset.mem_filter.mp hT).2
    simpa [hiS, hiT] using congrArg (fun U : Finset I => U.erase i) he
  · intro T hT
    have hiT := (Finset.mem_filter.mp hT).2
    exact ⟨T.erase i, by simp, Finset.insert_erase hiT⟩
  · intro S hS
    rfl

/-- The backward generator acts on an observable by actual local jumps. -/
def backward (k : Rates I) (f : Option (Finset I) → ℝ) : Option (Finset I) → ℝ
  | none => k.theta * (f (some ∅) - f none)
  | some S => (if S = ∅ then k.eta * (f none - f (some S)) else 0) +
      ∑ i, if i ∈ S then k.b i * (f (some (S.erase i)) - f (some S))
        else k.a i * (f (some (insert i S)) - f (some S))

private theorem edge_to_backward (k : Rates I) (f p : Option (Finset I) → ℝ) :
    (∑ e : Option (I × Finset I), (f (dst e) - f (src e)) *
      ((up k e)^2 * p (src e) - (down k e)^2 * p (dst e))) =
      ∑ x, backward k f x * p x := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, src, dst, up, down,
    Real.sq_sqrt k.theta_pos.le, Real.sq_sqrt k.eta_pos.le]
  have hedge (i : I) :
      (∑ S : Finset I, (f (some (insert i S)) - f (some S)) *
        ((if i ∈ S then 0 else Real.sqrt (k.a i)) ^ 2 * p (some S) -
         (if i ∈ S then 0 else Real.sqrt (k.b i)) ^ 2 * p (some (insert i S)))) =
      ∑ S : Finset I, (if i ∈ S then k.b i * (f (some (S.erase i)) - f (some S))
        else k.a i * (f (some (insert i S)) - f (some S))) * p (some S) := by
    have hi := sum_insert i (fun S =>
      k.b i * (f (some (S.erase i)) - f (some S)) * p (some S))
    have hleft : (∑ S : Finset I, (f (some (insert i S)) - f (some S)) *
        ((if i ∈ S then 0 else Real.sqrt (k.a i)) ^ 2 * p (some S) -
         (if i ∈ S then 0 else Real.sqrt (k.b i)) ^ 2 * p (some (insert i S)))) =
        (∑ S : Finset I, if i ∈ S then 0 else
          k.a i * (f (some (insert i S)) - f (some S)) * p (some S)) +
        ∑ S : Finset I, if i ∉ S then
          k.b i * (f (some ((insert i S).erase i)) - f (some (insert i S))) *
            p (some (insert i S)) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hiS : i ∈ S
      · simp [hiS]
      · simp [hiS, Real.sq_sqrt (k.a_pos i).le, Real.sq_sqrt (k.b_pos i).le]
        ring
    rw [hleft, hi, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> ring
  simp_rw [hedge]
  rw [Finset.sum_comm]
  simp only [backward, Fintype.sum_option, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul, ite_mul]
  try simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    mul_ite, ite_mul, mul_zero]
  ring_nf
  simp <;> ring

theorem dual_backward (k : Rates I) (f p : Option (Finset I) → ℝ) :
    (∑ x, f x * (generator k *ᵥ p) x) = ∑ x, backward k f x * p x :=
  (generator_dual k f p).trans (edge_to_backward k f p)

/-- Total probability of active Boolean configurations. -/
def activeMass (p : ℝ → Option (Finset I) → ℝ) (t : ℝ) : ℝ :=
  ∑ S : Finset I, p t (some S)
/-- The occupancy is that of an actual site, excluding the inhibited state. -/
def occupancy (i : I) : Option (Finset I) → ℝ
  | none => 0
  | some S => if i ∈ S then 1 else 0
/-- Actual site marginal under the same full-chain law. -/
def margin (p : ℝ → Option (Finset I) → ℝ) (i : I) (t : ℝ) : ℝ :=
  ∑ x, occupancy i x * p t x
/-- Actual simultaneous occupancy under the same full-chain law. -/
def joint (p : ℝ → Option (Finset I) → ℝ) (i j : I) (t : ℝ) : ℝ :=
  ∑ x, (occupancy i x * occupancy j x) * p t x
/-- Unnormalized association conditional on being outside the inhibited state. -/
def association (p : ℝ → Option (Finset I) → ℝ) (i j : I) (t : ℝ) : ℝ :=
  activeMass p t * joint p i j t - margin p i t * margin p j t
/-- The exact width from the four actual marginal fiber constraints. -/
def fiberWidth (p : ℝ → Option (Finset I) → ℝ) (i j : I) (t : ℝ) : ℝ :=
  min (min (margin p i t) (margin p j t))
    (min (activeMass p t - margin p i t) (activeMass p t - margin p j t))

private theorem backward_margin (k : Rates I) (i : I) (x : Option (Finset I)) :
    backward k (occupancy i) x =
      k.a i * (match x with | none => 0 | some _ => 1) -
        (k.a i + k.b i) * occupancy i x := by
  cases x with
  | none => simp [backward, occupancy]
  | some S =>
    have hs : (∑ l : I, if l ∈ S then
        k.b l * (occupancy i (some (S.erase l)) - occupancy i (some S))
        else k.a l * (occupancy i (some (insert l S)) - occupancy i (some S))) =
        if i ∈ S then -k.b i else k.a i := by
      rw [Finset.sum_eq_single i]
      · by_cases hi : i ∈ S <;> simp [occupancy, hi]
      · intro l _ hli
        by_cases hi : i ∈ S <;> by_cases hl : l ∈ S <;>
          simp [occupancy, hi, hl, Ne.symm hli]
      · simp
    simp only [backward, hs]
    by_cases hempty : S = ∅
    · subst S; simp [occupancy]
    · simp only [hempty, ↓reduceIte, zero_add, occupancy]
      split_ifs <;> ring

private theorem backward_joint (k : Rates I) (i j : I) (hij : i ≠ j)
    (x : Option (Finset I)) :
    backward k (fun x => occupancy i x * occupancy j x) x =
      k.b j * 0 + k.a j * occupancy i x + k.a i * occupancy j x -
        (k.a i + k.b i + k.a j + k.b j) * (occupancy i x * occupancy j x) := by
  cases x with
  | none => simp [backward, occupancy]
  | some S =>
    have hs : (∑ l : I, if l ∈ S then
        k.b l * (occupancy i (some (S.erase l)) * occupancy j (some (S.erase l)) -
          occupancy i (some S) * occupancy j (some S))
        else k.a l * (occupancy i (some (insert l S)) * occupancy j (some (insert l S)) -
          occupancy i (some S) * occupancy j (some S))) =
        (if i ∈ S then -k.b i * occupancy j (some S) else k.a i * occupancy j (some S)) +
        (if j ∈ S then -k.b j * occupancy i (some S) else k.a j * occupancy i (some S)) := by
      calc
        _ = ∑ l : I, ((if l = i then
            (if i ∈ S then -k.b i * occupancy j (some S) else k.a i * occupancy j (some S)) else 0) +
            (if l = j then
            (if j ∈ S then -k.b j * occupancy i (some S) else k.a j * occupancy i (some S)) else 0)) := by
          apply Finset.sum_congr rfl
          intro l _
          by_cases hli : l = i <;> by_cases hlj : l = j <;>
            by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> by_cases hl : l ∈ S <;>
            simp_all [occupancy, eq_comm] <;> ring
        _ = _ := by simp [Finset.sum_add_distrib]
    simp only [backward, hs]
    by_cases hempty : S = ∅
    · subst S; simp [occupancy]
    · simp only [hempty, ↓reduceIte, zero_add, mul_zero, zero_add, occupancy]
      split_ifs <;> ring

private def activeIndicator : Option (Finset I) → ℝ
  | none => 0
  | some _ => 1

private theorem expect_deriv (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (f : Option (Finset I) → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u => ∑ x, f x * p u x) (∑ x, backward k f x * p t x) t := by
  rw [← dual_backward]
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => (hp.2 t ht x).const_mul (f x))

private theorem active_deriv (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (activeMass p) (k.theta * p t none - k.eta * p t (some ∅)) t := by
  have hd := expect_deriv k p hp (activeIndicator (I := I)) t ht
  convert hd using 1
  · funext u
    simp [activeMass, activeIndicator, Fintype.sum_option]
  · simp [backward, activeIndicator, Fintype.sum_option, mul_add,
      Finset.sum_add_distrib, eq_comm]
    ring

private theorem margin_deriv (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (i : I) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (margin p i) (-(k.a i + k.b i) * margin p i t +
      k.a i * activeMass p t) t := by
  apply (expect_deriv k p hp (occupancy i) t ht).congr_deriv
  simp_rw [backward_margin]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  simp [margin, activeMass, Fintype.sum_option]
  ring

private theorem joint_deriv (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (i j : I) (hij : i ≠ j) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (joint p i j) (-(k.a i + k.b i + k.a j + k.b j) * joint p i j t +
      (k.a j * margin p i t + k.a i * margin p j t)) t := by
  apply (expect_deriv k p hp (fun x => occupancy i x * occupancy j x) t ht).congr_deriv
  simp_rw [backward_joint k i j hij]
  simp only [mul_zero, zero_add, sub_mul, add_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  dsimp [margin, joint]
  ring

private theorem stationary_pair_moments (k : Rates I) (L : Option (Finset I) → ℝ)
    (hL : generator k *ᵥ L = 0) (i j : I) (hij : i ≠ j) :
    joint (fun _ => L) i j 0 = activeMass (fun _ => L) 0 *
      (k.a i / (k.a i + k.b i)) * (k.a j / (k.a j + k.b j)) ∧
    margin (fun _ => L) i 0 = activeMass (fun _ => L) 0 *
      (k.a i / (k.a i + k.b i)) ∧
    margin (fun _ => L) j 0 = activeMass (fun _ => L) 0 *
      (k.a j / (k.a j + k.b j)) := by
  let r := activeMass (fun _ => L) 0
  let X := margin (fun _ => L) i 0
  let Y := margin (fun _ => L) j 0
  let K := joint (fun _ => L) i j 0
  let u := k.a i + k.b i
  let v := k.a j + k.b j
  have hs (f : Option (Finset I) → ℝ) : (∑ x, backward k f x * L x) = 0 := by
    rw [← dual_backward, hL]
    simp
  have hr : (∑ x, (match x with | none => (0 : ℝ) | some _ => 1) * L x) = r := by
    simp [r, activeMass, Fintype.sum_option]
  have hX : u * X = k.a i * r := by
    have h := hs (occupancy i)
    simp_rw [backward_margin] at h
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
    rw [hr] at h
    change k.a i * r - u * X = 0 at h
    linarith
  have hY : v * Y = k.a j * r := by
    have h := hs (occupancy j)
    simp_rw [backward_margin] at h
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
    rw [hr] at h
    change k.a j * r - v * Y = 0 at h
    linarith
  have hK : (u + v) * K = k.a j * X + k.a i * Y := by
    have h := hs (fun x => occupancy i x * occupancy j x)
    simp_rw [backward_joint k i j hij] at h
    simp only [mul_zero, zero_add, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
    have hJ : (∑ x, occupancy i x * (occupancy j x * L x)) = K := by
      simp [K, joint, mul_assoc]
    rw [hJ] at h
    change k.a j * X + k.a i * Y -
      (k.a i * K + k.b i * K + k.a j * K + k.b j * K) = 0 at h
    dsimp [u, v]
    linarith
  have hu : 0 < u := add_pos (k.a_pos i) (k.b_pos i)
  have hv : 0 < v := add_pos (k.a_pos j) (k.b_pos j)
  have he : (u + v) * (K * u * v - r * k.a i * k.a j) = 0 := by
    linear_combination (u*v)*hK + (k.a j*v)*hX + (k.a i*u)*hY
  have heq : K * u * v = r * k.a i * k.a j :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt (add_pos hu hv)))
  refine ⟨?_, ?_, ?_⟩
  · change K = r * (k.a i / u) * (k.a j / v)
    field_simp [ne_of_gt hu, ne_of_gt hv]
    nlinarith [heq]
  · change X = r * (k.a i / u)
    field_simp [ne_of_gt hu]
    nlinarith [hX]
  · change Y = r * (k.a j / v)
    field_simp [ne_of_gt hv]
    nlinarith [hY]

private theorem total_mass (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (t : ℝ) (ht : 0 ≤ t) :
    p t none + activeMass p t = 1 := by
  have hd (u : ℝ) (hu : 0 ≤ u) : HasDerivAt (fun v => ∑ x, p v x) 0 u := by
    simpa [backward] using expect_deriv k p hp (fun _ => 1) u hu
  have he := SingleEntryFiveState.constant_on_nonneg _ hd t ht
  simpa [hp.1, activeMass, Fintype.sum_option] using he

/-- The actual matrix-exponential solution of the finite-state forward system. -/
def canonicalTrajectory (k : Rates I) (t : ℝ) (x : Option (Finset I)) : ℝ :=
  NormedSpace.exp (t • generator k) x none

open scoped Matrix.Norms.Operator in
private def entry (i j : Option (Finset I)) :
    Matrix (Option (Finset I)) (Option (Finset I)) ℝ →L[ℝ] ℝ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (continuous_apply j).comp (continuous_apply i)

private theorem canonical_forward (k : Rates I) : ForwardSolution k (canonicalTrajectory k) := by
  constructor
  · funext i
    simp [canonicalTrajectory, Matrix.one_apply, Pi.single_apply, eq_comm]
  · intro t _ i
    open scoped Matrix.Norms.Operator in
      have hd := (entry i none).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_exp_smul_const' (generator k) t)
      convert! hd using 1 <;>
        simp [canonicalTrajectory, entry, Matrix.mul_apply, mulVec, dotProduct, Function.comp_def]

private theorem exp_entry_nonneg (B : Matrix (Option (Finset I)) (Option (Finset I)) ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (i j : Option (Finset I)) : 0 ≤ NormedSpace.exp B i j := by
  have hpow (n : ℕ) : ∀ i j, 0 ≤ (B ^ n) i j := by
    induction n with
    | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hB k j))
  open scoped Matrix.Norms.Operator in
    have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).map (entry i j)
      (entry i j).continuous
    change 0 ≤ (entry i j) (NormedSpace.exp B)
    rw [← hs.tsum_eq]
    apply tsum_nonneg
    intro n
    change 0 ≤ (n.factorial : ℝ)⁻¹ * (B ^ n) i j
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (hpow n i j)

private theorem canonical_nonneg (k : Rates I) (t : ℝ) (ht : 0 ≤ t)
    (x : Option (Finset I)) : 0 ≤ canonicalTrajectory k t x := by
  let C := ∑ e : Option (I × Finset I), ((up k e)^2 + (down k e)^2)
  let B := generator k + C • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ)
  have hB : ∀ x y, 0 ≤ B x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      dsimp [B]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
        ↓reduceIte, mul_one, generator]
      dsimp [C]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_nonneg
      intro e _
      by_cases hxs : x = src e <;> by_cases hxd : x = dst e <;>
        simp_all <;> nlinarith [sq_nonneg (up k e), sq_nonneg (down k e)]
    · change 0 ≤ generator k x y + C * (if x = y then 1 else 0)
      simp only [hxy, ↓reduceIte, mul_zero, add_zero, generator]
      apply Finset.sum_nonneg
      intro e _
      by_cases hxs : x = src e <;> by_cases hxd : x = dst e <;>
        by_cases hys : y = src e <;> by_cases hyd : y = dst e <;>
        simp_all <;> nlinarith [sq_nonneg (up k e), sq_nonneg (down k e)]
  have hsplit : t • generator k = (-t * C) • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ) + t • B := by
    dsimp [B]
    rw [smul_add, smul_smul]
    module
  have hcomm : Commute ((-t * C) • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ)) (t • B) :=
    (Commute.one_left _).smul_left _
  have hscalar : NormedSpace.exp ((-t * C) • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ)) =
      Real.exp (-t * C) • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ) := by
    have he : (-t * C) • (1 : Matrix (Option (Finset I)) (Option (Finset I)) ℝ) =
        diagonal (fun _ => -t * C) := by
      ext j l
      simp [Matrix.one_apply, Matrix.diagonal]
    rw [he, Matrix.exp_diagonal]
    ext j l
    simp [Matrix.diagonal, Matrix.one_apply, ← Real.exp_eq_exp_ℝ]
  unfold canonicalTrajectory
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, hscalar, Matrix.smul_mul, one_mul]
  exact mul_nonneg (Real.exp_pos _).le
    (exp_entry_nonneg (t • B) (fun j l => mul_nonneg ht (hB j l)) x none)

/-- The generator and the repressed initial state force strict association of
any two distinct sites in every finite Boolean network. The four fiber-width
constraints and the positive return flux use the same full-chain trajectory. -/
private theorem strict_pair (k : Rates I) (p : ℝ → Option (Finset I) → ℝ)
    (hp : ForwardSolution k p) (i j : I) (hij : i ≠ j) (t : ℝ) (ht : 0 < t) :
    activeMass p t = 1 - p t none ∧
    0 < activeMass p t ∧ 0 < fiberWidth p i j t ∧ 0 < association p i j t ∧
    0 < k.theta * p t none - k.eta * p t (some ∅) ∧
    (∀ u, 0 ≤ u → HasDerivAt (association p i j)
      (-(k.a i + k.b i + k.a j + k.b j) * association p i j u +
        (k.theta * p u none - k.eta * p u (some ∅)) * joint p i j u) u) := by
  let f := fun u => k.theta * p u none - k.eta * p u (some ∅)
  let r := activeMass p
  let X := margin p i
  let Y := margin p j
  let K := joint p i j
  let D := association p i j
  let s := k.a i + k.b i + k.a j + k.b j
  have fpos (u : ℝ) (hu : 0 ≤ u) : 0 < f u := (spectral_data k p hp).1 u hu
  have r0 : r 0 = 0 := by simp [r, activeMass, hp.1]
  have X0 : X 0 = 0 := by simp [X, margin, occupancy, hp.1]
  have Y0 : Y 0 = 0 := by simp [Y, margin, occupancy, hp.1]
  have K0 : K 0 = 0 := by simp [K, joint, occupancy, hp.1]
  have D0 : D 0 = 0 := by
    change r 0 * K 0 - X 0 * Y 0 = 0
    rw [r0, X0]; ring
  have dr (u : ℝ) (hu : 0 ≤ u) : HasDerivAt r (f u) u := active_deriv k p hp u hu
  have dX (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt X (-(k.a i + k.b i) * X u + k.a i * r u) u :=
    margin_deriv k p hp i u hu
  have dY (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt Y (-(k.a j + k.b j) * Y u + k.a j * r u) u :=
    margin_deriv k p hp j u hu
  have dK (u : ℝ) (hu : 0 ≤ u) :
      HasDerivAt K (-s * K u + (k.a j * X u + k.a i * Y u)) u :=
    joint_deriv k p hp i j hij u hu
  have rpos (u : ℝ) (hu : 0 < u) : 0 < r u := by
    apply SingleEntryFiveState.positive_forcing r f 0 r0 _
      (fun x hx => fpos x hx.le) u hu
    intro x hx; simpa using dr x hx
  have Xpos (u : ℝ) (hu : 0 < u) : 0 < X u :=
    SingleEntryFiveState.positive_forcing X (fun x => k.a i * r x) (k.a i + k.b i)
      X0 dX (fun x hx => mul_pos (k.a_pos i) (rpos x hx)) u hu
  have Ypos (u : ℝ) (hu : 0 < u) : 0 < Y u :=
    SingleEntryFiveState.positive_forcing Y (fun x => k.a j * r x) (k.a j + k.b j)
      Y0 dY (fun x hx => mul_pos (k.a_pos j) (rpos x hx)) u hu
  have rXpos (u : ℝ) (hu : 0 < u) : 0 < r u - X u := by
    apply SingleEntryFiveState.positive_forcing (fun x => r x - X x)
      (fun x => k.b i * r x + f x) (k.a i + k.b i) (by rw [r0, X0]; ring) _
      (fun x hx => add_pos (mul_pos (k.b_pos i) (rpos x hx)) (fpos x hx.le)) u hu
    intro x hx
    convert (dr x hx).sub (dX x hx) using 1 <;> ring
  have rYpos (u : ℝ) (hu : 0 < u) : 0 < r u - Y u := by
    apply SingleEntryFiveState.positive_forcing (fun x => r x - Y x)
      (fun x => k.b j * r x + f x) (k.a j + k.b j) (by rw [r0, Y0]; ring) _
      (fun x hx => add_pos (mul_pos (k.b_pos j) (rpos x hx)) (fpos x hx.le)) u hu
    intro x hx
    convert (dr x hx).sub (dY x hx) using 1 <;> ring
  have Kpos (u : ℝ) (hu : 0 < u) : 0 < K u :=
    SingleEntryFiveState.positive_forcing K (fun x => k.a j * X x + k.a i * Y x)
      s K0 dK (fun x hx => add_pos (mul_pos (k.a_pos j) (Xpos x hx))
        (mul_pos (k.a_pos i) (Ypos x hx))) u hu
  have dD (u : ℝ) (hu : 0 ≤ u) : HasDerivAt D (-s * D u + f u * K u) u := by
    convert ((dr u hu).mul (dK u hu)).sub ((dX u hu).mul (dY u hu)) using 1
    all_goals first | rfl | (dsimp [D, association, r, X, Y, K, s]; ring)
  have Dpos : 0 < D t := SingleEntryFiveState.positive_forcing D (fun u => f u * K u)
    s D0 dD (fun u hu => mul_pos (fpos u hu.le) (Kpos u hu)) t ht
  refine ⟨by have hm := total_mass k p hp t ht.le; linarith, rpos t ht, ?_, Dpos,
    fpos t ht.le, dD⟩
  simp only [fiberWidth, lt_min_iff]
  exact ⟨⟨Xpos t ht, Ypos t ht⟩, rXpos t ht, rYpos t ht⟩

/-- A probability-valued law exists, and every forward solution from the
inhibited state has strict association for every distinct site pair. -/
theorem finite_network_strict_pair (k : Rates I) :
    (∃ p : ℝ → Option (Finset I) → ℝ, ForwardSolution k p ∧
      ∀ u, 0 ≤ u → (∀ x, 0 ≤ p u x) ∧ p u none + activeMass p u = 1) ∧
    ∀ (p : ℝ → Option (Finset I) → ℝ), ForwardSolution k p →
      ∀ (i j : I), i ≠ j → ∀ t, 0 < t →
      activeMass p t = 1 - p t none ∧
      0 < activeMass p t ∧ 0 < fiberWidth p i j t ∧ 0 < association p i j t ∧
      0 < k.theta * p t none - k.eta * p t (some ∅) ∧
      (∀ u, 0 ≤ u → HasDerivAt (association p i j)
        (-(k.a i + k.b i + k.a j + k.b j) * association p i j u +
          (k.theta * p u none - k.eta * p u (some ∅)) * joint p i j u) u) ∧
      ∃ L : Option (Finset I) → ℝ,
        (∀ x, Tendsto (fun u => p u x) atTop (nhds (L x))) ∧ generator k *ᵥ L = 0 ∧
        joint (fun _ => L) i j 0 = activeMass (fun _ => L) 0 *
          (k.a i / (k.a i + k.b i)) * (k.a j / (k.a j + k.b j)) ∧
        margin (fun _ => L) i 0 = activeMass (fun _ => L) 0 *
          (k.a i / (k.a i + k.b i)) ∧
        margin (fun _ => L) j 0 = activeMass (fun _ => L) 0 *
          (k.a j / (k.a j + k.b j)) := by
  constructor
  · refine ⟨canonicalTrajectory k, canonical_forward k, ?_⟩
    intro u hu
    exact ⟨canonical_nonneg k u hu, total_mass k _ (canonical_forward k) u hu⟩
  · intro p hp i j hij t ht
    obtain ⟨ha, hr, hw, hD, hf, hODE⟩ := strict_pair k p hp i j hij t ht
    obtain ⟨L, hlim, hstat⟩ := (spectral_data k p hp).2.2
    exact ⟨ha, hr, hw, hD, hf, hODE, L, hlim, hstat,
      stationary_pair_moments k L hstat i j hij⟩

#print axioms dual_backward
#print axioms finite_network_strict_pair

end D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
