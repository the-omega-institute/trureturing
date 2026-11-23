/- GID: D5/S3/Fourier/Concentration/FiniteSpectralPerturbation
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteSpectralPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite spectral perturbations control weighted near-collisions at positive resolution. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Bounds for finite perturbations of positive-resolution collision mass. -/

set_option autoImplicit false

noncomputable section

open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

namespace D5.S3.Fourier.Concentration.FiniteSpectralPerturbation

private theorem affine_hit_count {M : ℕ} (a b : ℝ) {η : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) :
    (((range M).filter (fun k : ℕ => |a * (k : ℝ) + b| ≤ η)).card : ℝ) ≤
      1 + 2 * η / |a| := by
  let hits := (range M).filter (fun k : ℕ => |a * (k : ℝ) + b| ≤ η)
  by_cases hn : hits.Nonempty
  · let lo := hits.min' hn
    let hi := hits.max' hn
    have hle : lo ≤ hi := min'_le_max' hits hn
    have hsubset : hits ⊆ Icc lo hi := fun k hk =>
      mem_Icc.mpr ⟨min'_le hits k hk, le_max' hits k hk⟩
    have hcount := card_le_card hsubset
    rw [Nat.card_Icc] at hcount
    have hb0 : |a * (lo : ℝ) + b| ≤ η := (mem_filter.mp (min'_mem hits hn)).2
    have hb1 : |a * (hi : ℝ) + b| ≤ η := (mem_filter.mp (max'_mem hits hn)).2
    have hdiff : |a| * ((hi : ℝ) - (lo : ℝ)) ≤ 2 * η := by
      have ht := abs_sub_le (a * (hi : ℝ) + b) 0 (a * (lo : ℝ) + b)
      rw [sub_zero, zero_sub, abs_neg] at ht
      have hb := ht.trans (add_le_add hb1 hb0)
      rw [show a * (hi : ℝ) + b - (a * (lo : ℝ) + b) =
          a * ((hi : ℝ) - (lo : ℝ)) by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))] at hb
      linarith only [hb]
    have hr : (hi : ℝ) - (lo : ℝ) ≤ 2 * η / |a| := by
      apply (le_div_iff₀ (abs_pos.mpr ha)).2
      simpa only [mul_comm] using hdiff
    have hc : (hits.card : ℝ) ≤ ((hi + 1 - lo : ℕ) : ℝ) := by exact_mod_cast hcount
    rw [Nat.cast_sub (hle.trans (Nat.le_succ _)), Nat.cast_succ] at hc
    change (hits.card : ℝ) ≤ _
    linarith only [hc, hr]
  · have hz : hits = ∅ := not_nonempty_iff_eq_empty.mp hn
    change (hits.card : ℝ) ≤ _
    rw [hz, card_empty, Nat.cast_zero]
    positivity

private theorem affine_fin_hit_count {M : ℕ} (a b : ℝ) {η : ℝ}
    (ha : a ≠ 0) (hη : 0 ≤ η) :
    (((univ : Finset (Fin M)).filter (fun k => |a * (k.val : ℝ) + b| ≤ η)).card : ℝ) ≤
      1 + 2 * η / |a| := by
  let embedding : Fin M ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let test (k : ℕ) := |a * (k : ℝ) + b| ≤ η
  have hmap : ((univ : Finset (Fin M)).filter (fun k => test k.val)).map embedding =
      (range M).filter test := by
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, heq⟩ := mem_map.mp hk
      exact mem_filter.mpr ⟨mem_range.mpr (heq ▸ j.isLt), heq ▸ (mem_filter.mp hj).2⟩
    · intro hk
      obtain ⟨hM, htest⟩ := mem_filter.mp hk
      exact mem_map.mpr ⟨⟨k, mem_range.mp hM⟩, mem_filter.mpr ⟨mem_univ _, htest⟩, rfl⟩
  have hc := congrArg card hmap
  rw [card_map] at hc
  change (↑((univ : Finset (Fin M)).filter (fun k => test k.val)).card : ℝ) ≤ _
  rw [hc]
  exact affine_hit_count a b ha hη

private def offset {M : ℕ} (ε : ℝ) (k : Fin (M + 2)) : ℝ :=
  ε * (2 * (k.val : ℝ) / ((M : ℝ) + 1) - 1)

private theorem offset_abs_le {M : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (k : Fin (M + 2)) :
    |offset ε k| ≤ ε := by
  have hd : 0 < (M : ℝ) + 1 := by positivity
  have hk : (k.val : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast show k.val ≤ M + 1 by omega
  have hlow : 0 ≤ 2 * (k.val : ℝ) / ((M : ℝ) + 1) := by positivity
  have hhigh : 2 * (k.val : ℝ) / ((M : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ hd).2
    linarith
  apply abs_le.mpr
  unfold offset
  constructor
  · nlinarith only [mul_nonneg hε hlow]
  · nlinarith only [mul_nonneg hε (sub_nonneg.mpr hhigh)]

private theorem axis_affine {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (g c : J → ℝ) (ε : ℝ) (i : J) (other : {j // j ≠ i} → Fin (M + 2)) :
    ∃ b : ℝ, ∀ k : Fin (M + 2),
      (∑ j, c j * (g j + offset ε ((Equiv.funSplitAt i (Fin (M + 2))).symm (k, other) j))) =
        (c i * (2 * ε / ((M : ℝ) + 1))) * (k.val : ℝ) + b := by
  let s : Finset J := univ.erase i
  let f (k : Fin (M + 2)) (j : J) := (Equiv.funSplitAt i (Fin (M + 2))).symm (k, other) j
  let b := c i * (g i - ε) + ∑ j ∈ s, c j * (g j + offset ε (f 0 j))
  refine ⟨b, fun k => ?_⟩
  have heq : f k i = k := by simp [f, Equiv.funSplitAt, Equiv.piSplitAt]
  have hrest (j : J) (hj : j ∈ s) : f k j = f 0 j := by
    have hne := (mem_erase.mp hj).1
    simp [f, Equiv.funSplitAt, Equiv.piSplitAt, hne]
  have hsum :
      (∑ j, c j * (g j + offset ε (f k j))) =
        (∑ j ∈ s, c j * (g j + offset ε (f k j))) + c i * (g i + offset ε k) := by
    simpa only [s, heq] using
      (sum_erase_add univ (fun j => c j * (g j + offset ε (f k j))) (mem_univ i)).symm
  have hreplace : (∑ j ∈ s, c j * (g j + offset ε (f k j))) =
      ∑ j ∈ s, c j * (g j + offset ε (f 0 j)) := by
    exact sum_congr rfl fun j hj => by rw [hrest j hj]
  change (∑ j, c j * (g j + offset ε (f k j))) = _
  rw [hsum, hreplace]
  dsimp [b, offset]
  ring

private theorem sum_hit_le {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (g : J → ℝ) (c : J → ℤ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (i : J) (hi : c i ≠ 0) :
    (∑ f : J → Fin (M + 2),
      if |∑ j, (c j : ℝ) * (g j + offset ε (f j))| ≤ η then (1 : ℝ) else 0) ≤
      (Fintype.card (J → Fin (M + 2)) : ℝ) *
        (((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ) / (M + 2)) := by
  let e := Equiv.funSplitAt i (Fin (M + 2))
  let A := ({j // j ≠ i} → Fin (M + 2))
  let t : ℝ := 2 * ε / ((M : ℝ) + 1)
  let α : ℝ := (min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ)
  have hd : 0 < (M : ℝ) + 1 := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hcast : (c i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hmin : 1 ≤ |(c i : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hi)
  let I (f : J → Fin (M + 2)) : ℝ :=
    if |∑ j, (c j : ℝ) * (g j + offset ε (f j))| ≤ η then 1 else 0
  have hsplit : (∑ f, I f) = ∑ other : A, ∑ k : Fin (M + 2), I (e.symm (k, other)) := by
    calc
      _ = ∑ z : Fin (M + 2) × A, I (e.symm z) :=
        Fintype.sum_equiv e _ _ fun f => by simp
      _ = _ := Fintype.sum_prod_type_right' (fun k other => I (e.symm (k, other)))
  have hfiber (other : A) : (∑ k : Fin (M + 2), I (e.symm (k, other))) ≤ α := by
    obtain ⟨b, hb⟩ := axis_affine g (fun j => (c j : ℝ)) ε i other
    let a : ℝ := (c i : ℝ) * t
    have ha : a ≠ 0 := mul_ne_zero hcast ht.ne'
    have habs : t ≤ |a| := by
      dsimp [a]
      rw [abs_mul, abs_of_pos ht]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmin ht.le
    have hη' : 2 * η / t = η * ((M : ℝ) + 1) / ε := by
      dsimp [t]
      field_simp
    unfold I
    dsimp only [e]
    simp only [hb]
    change (∑ k : Fin (M + 2), if |a * (k.val : ℝ) + b| ≤ η then (1 : ℝ) else 0) ≤ α
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    let hits := (univ : Finset (Fin (M + 2))).filter (fun k => |a * (k.val : ℝ) + b| ≤ η)
    have hreal : (hits.card : ℝ) ≤ 1 + η * ((M : ℝ) + 1) / ε := by
      rw [← hη']
      have hh := div_le_div_of_nonneg_left (show 0 ≤ 2 * η by positivity) ht habs
      have hcount := affine_fin_hit_count a b ha hη (M := M + 2)
      change (hits.card : ℝ) ≤ _ at hcount
      linarith only [hcount, hh]
    have hfloor : hits.card ≤ 1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊ := by
      have hnonneg : 0 ≤ η * ((M : ℝ) + 1) / ε := by positivity
      calc
        _ ≤ ⌊1 + η * ((M : ℝ) + 1) / ε⌋₊ := Nat.le_floor hreal
        _ = _ := by rw [add_comm (1 : ℝ), Nat.floor_add_one hnonneg, add_comm]
    have hgrid : hits.card ≤ M + 2 := by
      simpa using (card_filter_le (univ : Finset (Fin (M + 2))) _)
    change (hits.card : ℝ) ≤
      ((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ)
    exact Nat.cast_le.mpr (le_min hgrid hfloor)
  have hcard : Fintype.card (J → Fin (M + 2)) = (M + 2) * Fintype.card A := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr e
  change (∑ f, I f) ≤ _
  rw [hsplit, hcard]
  calc
    _ ≤ ∑ _ : A, α := sum_le_sum fun other _ => hfiber other
    _ = (↑((M + 2) * Fintype.card A) : ℝ) * (α / (M + 2)) := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      have hM : (M : ℝ) + 2 ≠ 0 := by positivity
      field_simp

private theorem sum_pair_le {J : Type*} [Fintype J] [DecidableEq J] {M : ℕ}
    (g : J → ℝ) (m n : J → ℕ) (hmn : m ≠ n) {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η) :
    (∑ f : J → Fin (M + 2), if
        |monomialFrequency (fun j => g j + offset ε (f j)) m -
         monomialFrequency (fun j => g j + offset ε (f j)) n| ≤ η
        then (1 : ℝ) else 0) ≤
      (Fintype.card (J → Fin (M + 2)) : ℝ) *
        (((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ) / (M + 2)) := by
  have hcoord : ∃ i, m i ≠ n i := by
    by_contra! h
    exact hmn (funext h)
  obtain ⟨i, hi⟩ := hcoord
  let c : J → ℤ := fun j => (m j : ℤ) - (n j : ℤ)
  have hci : c i ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hi
  have hid (f : J → Fin (M + 2)) :
      monomialFrequency (fun j => g j + offset ε (f j)) m -
        monomialFrequency (fun j => g j + offset ε (f j)) n =
        ∑ j, (c j : ℝ) * (g j + offset ε (f j)) := by
    unfold monomialFrequency
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp [c]
    push_cast
    ring
  simp_rw [hid]
  exact sum_hit_le g c hε hη i hci

/-- One assignment of finite frequency offsets bounds the weighted off-diagonal collisions. -/
theorem exists_nearby_collision_bound {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p M : ℕ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η) :
    let W := ∑ j, w j
    let D := ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2
    ∃ g' : J → ℝ,
      (∀ j, |g' j - g j| ≤ ε) ∧
      (∃ f : J → Fin (M + 2), ∀ j,
        g' j = g j + ε * (2 * ((f j).val : ℝ) / ((M : ℝ) + 1) - 1)) ∧
      tailCollisionMass g' w p η ≤
        D + (((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ) / (M + 2)) *
          (W ^ (2 * p) - D) := by
  classical
  intro W D
  let A := J → Fin (M + 2)
  let S := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let Q : ℝ := Fintype.card A
  let α : ℝ := ((min (M + 2) (1 + ⌊η * ((M : ℝ) + 1) / ε⌋₊) : ℕ) : ℝ) / (M + 2)
  let x (f : A) (m : J → ℕ) : ℝ := monomialFrequency (fun j => g j + offset ε (f j)) m
  let E (f : A) := tailCollisionMass (fun j => g j + offset ε (f j)) w p η
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
      exact sum_pair_le g m n hmn hε hη
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
  have hbound : (∑ f : A, E f) ≤ Q * (D + α * (W ^ (2 * p) - D)) := by
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
  have hex : ∃ f : A, E f ≤ D + α * (W ^ (2 * p) - D) := by
    by_contra! hall
    have hlt := sum_lt_sum_of_nonempty (s := (univ : Finset A))
      univ_nonempty (fun f _ => hall f)
    simp only [sum_const, card_univ, nsmul_eq_mul] at hlt
    exact (not_lt_of_ge hbound) hlt
  obtain ⟨f, hf⟩ := hex
  refine ⟨fun j => g j + offset ε (f j), fun j => ?_, ⟨f, fun _ => rfl⟩, hf⟩
  rw [add_sub_cancel_left]
  exact offset_abs_le hε.le (f j)

#print axioms exists_nearby_collision_bound

end D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
