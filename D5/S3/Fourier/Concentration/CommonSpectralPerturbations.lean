/- GID: D5/S3/Fourier/Concentration/CommonSpectralPerturbations
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CommonSpectralPerturbations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable moment budgets give a common choice of finite spectral offsets. -/

import D5.S3.Fourier.Concentration.FiniteSpectralPerturbation

/-! A finite common-choice estimate for nonnegative spectral moment excesses. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

namespace D5.S3.Fourier.Concentration.CommonSpectralPerturbations

private theorem axis_affine {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (g c ε : J → ℝ) (i : J)
    (other : (j : {j // j ≠ i}) → Fin (M j + 2)) :
    ∃ b : ℝ, ∀ k : Fin (M i + 2),
      (∑ j, c j * (g j + offset (ε j) ((Equiv.piSplitAt i (fun j => Fin (M j + 2))).symm (k, other) j))) =
        (c i * (2 * ε i / ((M i : ℝ) + 1))) * (k.val : ℝ) + b := by
  let s : Finset J := univ.erase i
  let f (k : Fin (M i + 2)) (j : J) := (Equiv.piSplitAt i (fun j => Fin (M j + 2))).symm (k, other) j
  let b := c i * (g i - ε i) + ∑ j ∈ s, c j * (g j + offset (ε j) (f 0 j))
  refine ⟨b, fun k => ?_⟩
  have heq : f k i = k := by simp [f, Equiv.piSplitAt]
  have hrest (j : J) (hj : j ∈ s) : f k j = f 0 j := by
    have hne := (mem_erase.mp hj).1
    simp [f, Equiv.piSplitAt, hne]
  have hsum :
      (∑ j, c j * (g j + offset (ε j) (f k j))) =
        (∑ j ∈ s, c j * (g j + offset (ε j) (f k j))) + c i * (g i + offset (ε i) k) := by
    simpa only [s, heq] using
      (sum_erase_add univ (fun j => c j * (g j + offset (ε j) (f k j))) (mem_univ i)).symm
  have hreplace : (∑ j ∈ s, c j * (g j + offset (ε j) (f k j))) =
      ∑ j ∈ s, c j * (g j + offset (ε j) (f 0 j)) := by
    exact sum_congr rfl fun j hj => by rw [hrest j hj]
  change (∑ j, c j * (g j + offset (ε j) (f k j))) = _
  rw [hsum, hreplace]
  dsimp [b, offset]
  ring

private theorem sum_hit_le {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (g ε : J → ℝ) (c : J → ℤ) {η : ℝ} (hη : 0 ≤ η)
    (i : J) (hi : c i ≠ 0) (hε : 0 < ε i) :
    (∑ f : (j : J) → Fin (M j + 2),
      if |∑ j, (c j : ℝ) * (g j + offset (ε j) (f j))| ≤ η then (1 : ℝ) else 0) ≤
      (Fintype.card ((j : J) → Fin (M j + 2)) : ℝ) *
        (((min (M i + 2) (1 + ⌊η * ((M i : ℝ) + 1) / ε i⌋₊) : ℕ) : ℝ) / (M i + 2)) := by
  let e := Equiv.piSplitAt i (fun j => Fin (M j + 2))
  let A := ((j : {j // j ≠ i}) → Fin (M j + 2))
  let t : ℝ := 2 * ε i / ((M i : ℝ) + 1)
  let α : ℝ := (min (M i + 2) (1 + ⌊η * ((M i : ℝ) + 1) / ε i⌋₊) : ℕ)
  have hd : 0 < (M i : ℝ) + 1 := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hcast : (c i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hmin : 1 ≤ |(c i : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hi)
  let I (f : (j : J) → Fin (M j + 2)) : ℝ :=
    if |∑ j, (c j : ℝ) * (g j + offset (ε j) (f j))| ≤ η then 1 else 0
  have hsplit : (∑ f, I f) = ∑ other : A, ∑ k : Fin (M i + 2), I (e.symm (k, other)) := by
    calc
      _ = ∑ z : Fin (M i + 2) × A, I (e.symm z) :=
        Fintype.sum_equiv e _ _ fun f => by simp
      _ = _ := Fintype.sum_prod_type_right' (fun k other => I (e.symm (k, other)))
  have hfiber (other : A) : (∑ k : Fin (M i + 2), I (e.symm (k, other))) ≤ α := by
    obtain ⟨b, hb⟩ := axis_affine M g (fun j => (c j : ℝ)) ε i other
    let a : ℝ := (c i : ℝ) * t
    have ha : a ≠ 0 := mul_ne_zero hcast ht.ne'
    have habs : t ≤ |a| := by
      dsimp [a]
      rw [abs_mul, abs_of_pos ht]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmin ht.le
    have hη' : 2 * η / t = η * ((M i : ℝ) + 1) / ε i := by
      dsimp [t]
      field_simp
    unfold I
    dsimp only [e]
    simp only [hb]
    change (∑ k : Fin (M i + 2), if |a * (k.val : ℝ) + b| ≤ η then (1 : ℝ) else 0) ≤ α
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    let hits := (univ : Finset (Fin (M i + 2))).filter (fun k => |a * (k.val : ℝ) + b| ≤ η)
    have hreal : (hits.card : ℝ) ≤ 1 + η * ((M i : ℝ) + 1) / ε i := by
      rw [← hη']
      have hh := div_le_div_of_nonneg_left (show 0 ≤ 2 * η by positivity) ht habs
      have hcount := affine_fin_hit_count a b ha hη (M := M i + 2)
      change (hits.card : ℝ) ≤ _ at hcount
      linarith only [hcount, hh]
    have hfloor : hits.card ≤ 1 + ⌊η * ((M i : ℝ) + 1) / ε i⌋₊ := by
      have hnonneg : 0 ≤ η * ((M i : ℝ) + 1) / ε i := by positivity
      calc
        _ ≤ ⌊1 + η * ((M i : ℝ) + 1) / ε i⌋₊ := Nat.le_floor hreal
        _ = _ := by rw [add_comm (1 : ℝ), Nat.floor_add_one hnonneg, add_comm]
    have hgrid : hits.card ≤ M i + 2 := by
      simpa using (card_filter_le (univ : Finset (Fin (M i + 2))) _)
    change (hits.card : ℝ) ≤
      ((min (M i + 2) (1 + ⌊η * ((M i : ℝ) + 1) / ε i⌋₊) : ℕ) : ℝ)
    exact Nat.cast_le.mpr (le_min hgrid hfloor)
  have hcard : Fintype.card ((j : J) → Fin (M j + 2)) = (M i + 2) * Fintype.card A := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr e
  change (∑ f, I f) ≤ _
  rw [hsplit, hcard]
  calc
    _ ≤ ∑ _ : A, α := sum_le_sum fun other _ => hfiber other
    _ = (↑((M i + 2) * Fintype.card A) : ℝ) * (α / (M i + 2)) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      have hM : (M i : ℝ) + 2 ≠ 0 := by positivity
      field_simp

private theorem sum_pair_le {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (g ε : J → ℝ) (m n : J → ℕ) (hmn : m ≠ n)
    {η ρ : ℝ} (hε : ∀ i, 0 < ε i) (hη : 0 ≤ η)
    (hρ : ∀ i, (((min (M i + 2) (1 + ⌊η * ((M i : ℝ) + 1) / ε i⌋₊) : ℕ) : ℝ) / (M i + 2)) ≤ ρ) :
    (∑ f : (j : J) → Fin (M j + 2), if
        |monomialFrequency (fun j => g j + offset (ε j) (f j)) m -
         monomialFrequency (fun j => g j + offset (ε j) (f j)) n| ≤ η
        then (1 : ℝ) else 0) ≤
      (Fintype.card ((j : J) → Fin (M j + 2)) : ℝ) *
        ρ := by
  have hcoord : ∃ i, m i ≠ n i := by
    by_contra! h
    exact hmn (funext h)
  obtain ⟨i, hi⟩ := hcoord
  let c : J → ℤ := fun j => (m j : ℤ) - (n j : ℤ)
  have hci : c i ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hi
  have hid (f : (j : J) → Fin (M j + 2)) :
      monomialFrequency (fun j => g j + offset (ε j) (f j)) m -
        monomialFrequency (fun j => g j + offset (ε j) (f j)) n =
        ∑ j, (c j : ℝ) * (g j + offset (ε j) (f j)) := by
    unfold monomialFrequency
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp [c]
    push_cast
    ring
  simp_rw [hid]
  exact (sum_hit_le M g ε c hη i hci (hε i)).trans
    (mul_le_mul_of_nonneg_left (hρ i) (Nat.cast_nonneg _))

/-- A uniform fiber bound controls the mean collision mass on heterogeneous finite grids. -/
private theorem sum_grid_collisionMass_le {J : Type*} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (g w ε : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ)
    {η ρ : ℝ} (hε : ∀ j, 0 < ε j) (hη : 0 ≤ η)
    (hρ : ∀ j, (((min (M j + 2) (1 + ⌊η * ((M j : ℝ) + 1) / ε j⌋₊) : ℕ) : ℝ) /
      (M j + 2)) ≤ ρ) :
    let W := ∑ j, w j
    let D := ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2
    (∑ f : (j : J) → Fin (M j + 2),
      tailCollisionMass (fun j => g j + offset (ε j) (f j)) w p η) ≤
      (Fintype.card ((j : J) → Fin (M j + 2)) : ℝ) * (D + ρ * (W ^ (2 * p) - D)) := by
  classical
  intro W D
  let A := (j : J) → Fin (M j + 2)
  let S := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let Q : ℝ := Fintype.card A
  let α := ρ
  let x (f : A) (m : J → ℕ) : ℝ := monomialFrequency (fun j => g j + offset (ε j) (f j)) m
  let E (f : A) := tailCollisionMass (fun j => g j + offset (ε j) (f j)) w p η
  let Mpair (m n : J → ℕ) : ℝ := ∑ f : A, if |x f m - x f n| ≤ η then 1 else 0
  have hc (m : J → ℕ) : 0 ≤ c m := monomialWeight_nonneg w hw m
  have hmass : (∑ m ∈ S, c m) = W ^ p := by
    symm
    exact sum_pow_eq_sum_piAntidiag univ w p
  have hpair (m n : J → ℕ) : Mpair m n ≤ α * Q + if m = n then Q - α * Q else 0 := by
    by_cases hmn : m = n
    · subst n
      simp [Mpair, hη, Q]
    · simp only [hmn, ite_false, add_zero]
      rw [mul_comm]
      exact sum_pair_le M g ε m n hmn hε hη hρ
  have hreorder : (∑ f : A, E f) = ∑ m ∈ S, ∑ n ∈ S, c m * c n * Mpair m n := by
    change (∑ f : A, ∑ m ∈ S, ∑ n ∈ S, if |x f m - x f n| ≤ η then c m * c n else 0) = _
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun n _ => ?_
    unfold Mpair
    rw [mul_sum]
    refine sum_congr rfl fun f _ => ?_
    split_ifs <;> simp
  have hmain :
      (∑ m ∈ S, ∑ n ∈ S, c m * c n * (α * Q)) = α * Q * W ^ (2 * p) := by
    rw [mul_comm 2 p, pow_mul, ← hmass]
    simp only [pow_two, sum_mul, mul_sum, mul_assoc]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    ring
  have hdiag :
      (∑ m ∈ S, ∑ n ∈ S, if m = n then c m * c n * (Q - α * Q) else 0) =
        D * (Q - α * Q) := by
    change _ = (∑ m ∈ S, c m ^ 2) * (Q - α * Q)
    rw [sum_mul]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_eq_single m]
    · simp [pow_two]
    · intro n _ hne
      simp [Ne.symm hne]
    · intro hbad
      exact (hbad hm).elim
  change (∑ f : A, E f) ≤ Q * (D + α * (W ^ (2 * p) - D))
  rw [hreorder]
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        (c m * c n * (α * Q) + if m = n then c m * c n * (Q - α * Q) else 0) := by
      refine sum_le_sum fun m _ => sum_le_sum fun n _ => ?_
      have h := mul_le_mul_of_nonneg_left (hpair m n) (mul_nonneg (hc m) (hc n))
      simpa only [mul_add, mul_ite, mul_zero] using h
    _ = _ := by
      simp only [sum_add_distrib]
      rw [hmain, hdiag]
      ring

private theorem finite_common_choice {A K : Type*} [Fintype A] [Nonempty A]
    (tests : Finset K) (loss : K → A → ℝ) (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k ∈ tests, ∀ a, 0 ≤ loss k a)
    (hthreshold : ∀ k ∈ tests, 0 < threshold k)
    (hmean : ∀ k ∈ tests, (∑ a : A, loss k a) ≤ (Fintype.card A : ℝ) * meanBound k)
    (hbudget : (∑ k ∈ tests, meanBound k / threshold k) ≤ 1) :
    ∃ a : A, ∀ k ∈ tests, loss k a ≤ threshold k := by
  classical
  by_contra! h
  have hpointwise (a : A) : 1 < ∑ k ∈ tests, loss k a / threshold k := by
    obtain ⟨k, hk, hbad⟩ := h a
    have hone : 1 < loss k a / threshold k := by
      apply (lt_div_iff₀ (hthreshold k hk)).2
      simpa using hbad
    exact hone.trans_le (single_le_sum (f := fun i => loss i a / threshold i)
      (fun i hi => div_nonneg (hnonneg i hi a) (hthreshold i hi).le) hk)
  have hnormalized (k : K) (hk : k ∈ tests) :
      ∑ a : A, loss k a / threshold k ≤ (Fintype.card A : ℝ) * (meanBound k / threshold k) := by
    rw [← sum_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hmean k hk) (hthreshold k hk).le
  have hlt : (Fintype.card A : ℝ) < (Fintype.card A : ℝ) := by
    calc
      _ = ∑ _ : A, (1 : ℝ) := by simp
      _ < ∑ a : A, ∑ k ∈ tests, loss k a / threshold k :=
        sum_lt_sum_of_nonempty univ_nonempty fun a _ => hpointwise a
      _ = ∑ k ∈ tests, ∑ a : A, loss k a / threshold k := sum_comm
      _ ≤ ∑ k ∈ tests, (Fintype.card A : ℝ) * (meanBound k / threshold k) :=
        sum_le_sum hnormalized
      _ = (Fintype.card A : ℝ) * ∑ k ∈ tests, meanBound k / threshold k := (mul_sum ..).symm
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)
  exact (lt_irrefl _) hlt

private theorem lift_finite_mean {J : Type*} [DecidableEq J]
    (M : J → ℕ) {U V : Finset J} (hVU : V ⊆ U)
    (loss : ((j : V) → Fin (M j + 2)) → ℝ) {bound : ℝ}
    (hmean : (∑ x, loss x) ≤ (Fintype.card ((j : V) → Fin (M j + 2)) : ℝ) * bound) :
    (∑ x : ((j : U) → Fin (M j + 2)), loss (fun i : V => x ⟨i, hVU i.2⟩)) ≤
      (Fintype.card ((j : U) → Fin (M j + 2)) : ℝ) * bound := by
  classical
  let T := {j : U // (j : J) ∉ V}
  let From := (j : U) → Fin (M j + 2)
  let View := (j : V) → Fin (M j + 2)
  let Rest := (j : T) → Fin (M j.1 + 2)
  let part := Equiv.piEquivPiSubtypeProd (fun j : U => (j : J) ∈ V)
    (fun j : U => Fin (M j + 2))
  let index : {j : U // (j : J) ∈ V} ≃ V :=
    { toFun := fun j => ⟨j.1.val, j.2⟩
      invFun := fun j => ⟨⟨j.val, hVU j.2⟩, j.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let first := Equiv.piCongrLeft (fun j : V => Fin (M j + 2)) index
  let e : From ≃ View × Rest := part.trans (Equiv.prodCongr first (Equiv.refl Rest))
  have heq (x : From) : (e x).1 = fun j : V => x ⟨j, hVU j.2⟩ := by
    apply first.symm.injective
    funext j
    simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply, first,
      Equiv.symm_apply_apply, Equiv.piCongrLeft_symm_apply]
    rfl
  have hs : (∑ x : From, loss (fun i : V => x ⟨i, hVU i.2⟩)) =
      ∑ y : View × Rest, loss y.1 := by
    exact Fintype.sum_equiv e _ _ (fun x => congrArg loss (heq x).symm)
  have hcard : Fintype.card From = Fintype.card View * Fintype.card Rest := by
    simpa only [Fintype.card_prod] using Fintype.card_congr e
  change (∑ x : From, loss (fun i : V => x ⟨i, hVU i.2⟩)) ≤ (Fintype.card From : ℝ) * bound
  rw [hs, Fintype.sum_prod_type, hcard, Nat.cast_mul]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [mul_comm (Fintype.card View : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)

private theorem exists_for_finite_tests {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (support : K → Finset J) (tests : Finset K)
    (loss : ∀ k, (((j : support k) → Fin (M j + 2)) → ℝ))
    (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k ∈ tests, ∀ x, 0 ≤ loss k x)
    (hthreshold : ∀ k ∈ tests, 0 < threshold k)
    (hmean : ∀ k ∈ tests, (∑ x, loss k x) ≤
      (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * meanBound k)
    (hbudget : (∑ k ∈ tests, meanBound k / threshold k) ≤ 1) :
    ∃ x : (j : J) → Fin (M j + 2), ∀ k ∈ tests, loss k (fun j => x j) ≤ threshold k := by
  classical
  let U := tests.biUnion support
  have hsub (k : K) (hk : k ∈ tests) : support k ⊆ U :=
    fun _ hi => mem_biUnion.mpr ⟨k, hk, hi⟩
  let localLoss (k : K) (x : (j : U) → Fin (M j + 2)) : ℝ :=
    if hk : k ∈ tests then loss k (fun j => x ⟨j, hsub k hk j.2⟩) else 0
  have hlocalNonneg (k : K) (hk : k ∈ tests) (x : (j : U) → Fin (M j + 2)) :
      0 ≤ localLoss k x := by
    simpa only [localLoss, dite_eq_left hk] using hnonneg k hk (fun j => x ⟨j, hsub k hk j.2⟩)
  have hlocalMean (k : K) (hk : k ∈ tests) :
      (∑ x : (j : U) → Fin (M j + 2), localLoss k x)
        ≤ (Fintype.card ((j : U) → Fin (M j + 2)) : ℝ) * meanBound k := by
    simpa only [localLoss, dite_eq_left hk] using
      lift_finite_mean M (hsub k hk) (loss k) (hmean k hk)
  obtain ⟨x, hx⟩ :=
    finite_common_choice tests localLoss meanBound threshold
      hlocalNonneg hthreshold hlocalMean hbudget
  refine ⟨fun j => if hj : j ∈ U then x ⟨j, hj⟩ else 0, fun k hk => ?_⟩
  simpa only [localLoss, dite_eq_left hk, dite_eq_left (hsub k hk (Subtype.property _))] using hx k hk

private theorem exists_for_all_finite_support_tests {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (support : K → Finset J)
    (loss : ∀ k, (((j : support k) → Fin (M j + 2)) → ℝ))
    (meanBound threshold : K → ℝ)
    (hnonneg : ∀ k x, 0 ≤ loss k x)
    (hthreshold : ∀ k, 0 < threshold k)
    (hmean : ∀ k, (∑ x, loss k x) ≤
      (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * meanBound k)
    (hbudget : ∀ tests : Finset K, (∑ k ∈ tests, meanBound k / threshold k) ≤ 1) :
    ∃ x : (j : J) → Fin (M j + 2), ∀ k, loss k (fun j => x j) ≤ threshold k := by
  let good (k : K) : Set ((j : J) → Fin (M j + 2)) :=
    {x | loss k (fun j => x j) ≤ threshold k}
  have hclosed (k : K) : IsClosed (good k) := by
    change IsClosed ((Finset.restrict (π := fun j => Fin (M j + 2)) (support k)) ⁻¹'
      {y | loss k y ≤ threshold k})
    exact (isClosed_discrete _).preimage (Finset.continuous_restrict (support k))
  have hfinite (tests : Finset K) : (⋂ k ∈ tests, good k).Nonempty := by
    obtain ⟨x, hx⟩ := exists_for_finite_tests M support tests loss meanBound threshold
      (fun k _ => hnonneg k) (fun k _ => hthreshold k) (fun k _ => hmean k) (hbudget tests)
    exact ⟨x, Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk => hx k hk⟩
  obtain ⟨x, hx⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  exact ⟨x, fun k => Set.mem_iInter.mp hx k⟩

/-- The total weight available to distinct ordered pairs of degree vectors. -/
def offDiagonalMass {J : Type*} [Fintype J] [DecidableEq J]
    (w : J → ℝ) (p : ℕ) : ℝ :=
  (∑ j, w j) ^ (2 * p) - diagonal w p

private theorem collision_between {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    diagonal w p ≤ tailCollisionMass g w p η ∧
    tailCollisionMass g w p η ≤ (∑ j, w j) ^ (2 * p) := by
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let freq := monomialFrequency g
  let E (m n : J → ℕ) := if |freq m - freq n| ≤ η then c m * c n else 0
  have hc (m : J → ℕ) : 0 ≤ c m := monomialWeight_nonneg w hw m
  have hcSum : (∑ m ∈ s, c m) = (∑ j, w j) ^ p := by
    symm
    exact sum_pow_eq_sum_piAntidiag univ w p
  change (∑ m ∈ s, c m ^ 2) ≤ (∑ m ∈ s, ∑ n ∈ s, E m n) ∧
    (∑ m ∈ s, ∑ n ∈ s, E m n) ≤ (∑ j, w j) ^ (2 * p)
  constructor
  · apply sum_le_sum
    intro m hm
    have h := single_le_sum (f := E m) (fun n _ => by
      dsimp [E]
      split_ifs
      · exact mul_nonneg (hc m) (hc n)
      · exact le_rfl) hm
    simpa [E, pow_two, hη] using h
  · rw [mul_comm 2 p, pow_mul, ← hcSum]
    have hproduct : (∑ n ∈ s, c n) ^ 2 = ∑ m ∈ s, ∑ n ∈ s, c m * c n := by
      rw [pow_two, sum_mul]
      exact sum_congr rfl (fun m _ => mul_sum ..)
    rw [hproduct]
    apply sum_le_sum
    intro m _
    apply sum_le_sum
    intro n _
    dsimp [E]
    split_ifs
    · exact (le_rfl : c m * c n ≤ c m * c n)
    · exact mul_nonneg (hc m) (hc n)

/-- A single perturbation meets all the finite-resolution budgets in the family. -/
theorem exists_common_nearby_collision_bounds {J K : Type*} [DecidableEq J]
    (M : J → ℕ) (g ε : J → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ)
    (hw : ∀ k j, 0 ≤ w k j) (p : K → ℕ) (η ρ b : K → ℝ)
    (hη : ∀ k, 0 ≤ η k)
    (hb : ∀ k, 0 < offDiagonalMass (w k) (p k) → 0 < b k)
    (hgrid : ∀ k, 0 < offDiagonalMass (w k) (p k) → b k < 1 → ∀ j : support k,
      0 < ε j ∧ ((min (M j + 2) (1 + ⌊η k * ((M j : ℝ) + 1) / ε j⌋₊) : ℕ) : ℝ) /
        (M j + 2) ≤ ρ k)
    (hbudget : ∀ tests : Finset K, ∑ k ∈ tests,
      (if 0 < offDiagonalMass (w k) (p k) ∧ b k < 1 then ρ k / b k else 0) ≤ 1) :
    ∃ g' : J → ℝ, (∀ j, |g' j - g j| ≤ ε j) ∧
      (∃ f : (j : J) → Fin (M j + 2), ∀ j,
        g' j = g j + ε j * (2 * ((f j).val : ℝ) / ((M j : ℝ) + 1) - 1)) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        diagonal (w k) (p k) + b k * offDiagonalMass (w k) (p k) := by
  classical
  let D (k : K) := diagonal (w k) (p k)
  let B (k : K) := offDiagonalMass (w k) (p k)
  let active (k : K) := 0 < B k ∧ b k < 1
  let E (k : K) (x : (j : support k) → Fin (M j + 2)) :=
    tailCollisionMass (fun j : support k => g j + offset (ε j) (x j)) (w k) (p k) (η k)
  let loss (k : K) (x : (j : support k) → Fin (M j + 2)) :=
    if active k then (E k x - D k) / B k else 0
  let rate (k : K) := if active k then ρ k else 0
  let threshold (k : K) := if active k then b k else 1
  have hbetween (k : K) (x : (j : support k) → Fin (M j + 2)) :
      D k ≤ E k x ∧ E k x ≤ D k + B k := by
    have h := collision_between (fun j : support k => g j + offset (ε j) (x j))
      (w k) (hw k) (p k) (hη k)
    refine ⟨h.1, h.2.trans_eq ?_⟩
    dsimp [D, B, offDiagonalMass]
    ring
  have hnonneg (k : K) (x : (j : support k) → Fin (M j + 2)) : 0 ≤ loss k x := by
    dsimp only [loss]
    split_ifs with hk
    · exact div_nonneg (sub_nonneg.mpr (hbetween k x).1) hk.1.le
    · exact le_rfl
  have hthreshold (k : K) : 0 < threshold k := by
    dsimp only [threshold]
    split_ifs with hk
    · exact hb k hk.1
    · exact zero_lt_one
  have hmean (k : K) :
      (∑ x, loss k x) ≤ (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) * rate k := by
    by_cases hk : active k
    · have hbound : (∑ x, E k x) ≤
          (Fintype.card ((j : support k) → Fin (M j + 2)) : ℝ) *
            (D k + ρ k * B k) :=
        sum_grid_collisionMass_le (fun j : support k => M j)
          (fun j => g j) (w k) (fun j => ε j) (hw k) (p k)
          (fun j => (hgrid k hk.1 hk.2 j).1) (hη k) (fun j => (hgrid k hk.1 hk.2 j).2)
      simp only [loss, rate, ite_eq_left hk, ← sum_div, sum_sub_distrib, sum_const, card_univ,
        nsmul_eq_mul]
      apply (div_le_iff₀ hk.1).mpr
      linarith only [hbound]
    · simp [loss, rate, hk]
  have hbudget' (tests : Finset K) : ∑ k ∈ tests, rate k / threshold k ≤ 1 := by
    refine le_of_eq_of_le (sum_congr rfl ?_) (hbudget tests)
    intro k _
    change rate k / threshold k = (if active k then ρ k / b k else 0)
    by_cases hk : active k <;> simp [rate, threshold, hk]
  obtain ⟨x, hx⟩ := exists_for_all_finite_support_tests M support loss rate threshold
    hnonneg hthreshold hmean hbudget'
  refine ⟨fun j => g j + offset (ε j) (x j), ?_, ⟨x, fun _ => rfl⟩, ?_⟩
  · intro j
    rw [add_sub_cancel_left]
    exact offset_abs_le (hε j) (x j)
  · intro k
    change E k (fun j => x j) ≤ D k + b k * B k
    by_cases hk : active k
    · have hz := hx k
      simp only [loss, threshold, ite_eq_left hk] at hz
      rw [div_le_iff₀ hk.1] at hz
      linarith only [hz]
    · have hpair := hbetween k (fun j => x j)
      by_cases hpos : 0 < B k
      · have ht : 1 ≤ b k := le_of_not_gt fun hlt => hk ⟨hpos, hlt⟩
        exact hpair.2.trans (by nlinarith only [mul_le_mul_of_nonneg_right ht hpos.le])
      · have hzero : B k = 0 := le_antisymm (le_of_not_gt hpos) (by linarith only [hpair.1, hpair.2])
        simpa [hzero] using hpair.2

#print axioms exists_common_nearby_collision_bounds

end D5.S3.Fourier.Concentration.CommonSpectralPerturbations
