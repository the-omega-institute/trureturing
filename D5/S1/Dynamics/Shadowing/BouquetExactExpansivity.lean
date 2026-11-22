/- GID: D5/S1/Dynamics/Shadowing/BouquetExactExpansivity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/BouquetExactExpansivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Topologically exact dynamics of exact finite positive expansivity order on bouquets. -/

import D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness.Basic
import D5.S1.Dynamics.Shadowing.InvarianceGluedSheets
import Mathlib.Topology.Homeomorph.Quotient

/-!
A tour traverses each loop once in order. Its composition with the
projection that forgets the loop is a self-map of the bouquet.
-/

noncomputable section

open Function Set Topology

namespace D5.S1.Dynamics.Shadowing.BouquetExactExpansivity

open CircleFinitePositiveExpansiveness (Circle coordinate coordinate_mem project
  project_coordinate continuous_project project_dist_eq)
open InvarianceGluedSheets (lift)

variable {N : ℕ}

/-- The metric bouquet of `N` unit circles. -/
abbrev Space (N : ℕ) := InvarianceGluedSheets.Space N (fun x : Circle => dist x 0)

/-- Forget the sheet label. -/
def projection (p : Space N) : Circle := p.val.1

/-- The inclusion of each labelled copy of the circle. -/
def sheet (i : Fin N) (x : Circle) : Space N := lift (fun y => dist y 0) i x

@[simp] private theorem projection_sheet (i : Fin N) (x : Circle) :
    projection (sheet i x) = x := rfl

private theorem continuous_projection : Continuous (projection (N := N)) :=
  continuous_fst.comp continuous_subtype_val

private theorem continuous_sheet (i : Fin N) : Continuous (sheet i) :=
  (continuous_id.prodMk (continuous_const.mul (continuous_id.dist continuous_const))).subtype_mk _

private theorem exists_sheet (p : Space N) : ∃ i : Fin N, sheet i (projection p) = p := by
  obtain ⟨i, hi⟩ := p.property
  exact ⟨i, Subtype.ext (Prod.ext rfl hi.symm)⟩

private theorem sheet_zero (i j : Fin N) : sheet i 0 = sheet j 0 := by
  apply Subtype.ext
  change ((0 : Circle), (i.val : ℝ) * dist (0 : Circle) 0) =
    (0, (j.val : ℝ) * dist (0 : Circle) 0)
  simp

private theorem sheet_label_eq {i j : Fin N} {x : Circle} (hx : x ≠ 0)
    (h : sheet i x = sheet j x) : i = j := by
  have hheight : (i.val : ℝ) * dist x 0 = (j.val : ℝ) * dist x 0 :=
    congrArg (fun p : Space N => p.val.2) h
  have hlabel := mul_right_cancel₀ (dist_ne_zero.mpr hx) hheight
  exact Fin.ext (by exact_mod_cast hlabel)

/-- The relation that identifies precisely the zero points of the labelled circles. -/
def wedgeSetoid (N : ℕ) : Setoid (Fin N × Circle) where
  r a b := a = b ∨ (a.2 = 0 ∧ b.2 = 0)
  iseqv := ⟨fun a => Or.inl rfl, by
    rintro a b (rfl | ⟨ha, hb⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hb, ha⟩, by
    rintro a b c (rfl | ⟨ha, hb⟩) (rfl | ⟨hb', hc⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hb', hc⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩⟩

/-- The metric realization carries the quotient topology of the bouquet. -/
def wedgeHomeomorph (N : ℕ) : Quotient (wedgeSetoid N) ≃ₜ Space N := by
  let q : C(Fin N × Circle, Space N) :=
    ⟨fun a => sheet a.1 a.2, continuous_prod_of_discrete_left.mpr continuous_sheet⟩
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous (fun p => by
    obtain ⟨i, hi⟩ := exists_sheet p
    exact ⟨(i, projection p), hi⟩)
  have hker (a b : Fin N × Circle) : (wedgeSetoid N).r a b ↔ (Setoid.ker q).r a b := by
    change (a = b ∨ (a.2 = 0 ∧ b.2 = 0)) ↔ sheet a.1 a.2 = sheet b.1 b.2
    constructor
    · rintro (rfl | ⟨ha, hb⟩)
      · rfl
      · rw [ha, hb, sheet_zero]
    · intro h
      have hab : a.2 = b.2 := congrArg projection h
      by_cases ha : a.2 = 0
      · exact Or.inr ⟨ha, hab.symm.trans ha⟩
      · have h' : sheet a.1 a.2 = sheet b.1 a.2 := by rwa [hab] at h ⊢
        exact Or.inl (Prod.ext (sheet_label_eq ha h') hab)
  exact (Homeomorph.Quotient.congrRight hker).trans hq.homeomorph

private theorem compactSpace_space (N : ℕ) : CompactSpace (Space N) :=
  InvarianceGluedSheets.compactSpace_space (continuous_id.dist continuous_const)

private theorem project_zero : project 0 = 0 := AddCircle.coe_zero 1
private theorem project_one : project 1 = 0 := AddCircle.coe_period 1

private theorem project_nat_add (i : ℕ) (t : ℝ) : project ((i : ℝ) + t) = project t := by
  have hi : ((i : ℝ) : Circle) = 0 := by
    calc
      _ = ((i • (1 : ℝ) : ℝ) : Circle) := by simp [nsmul_eq_mul]
      _ = i • ((1 : ℝ) : Circle) := AddCircle.coe_nsmul 1
      _ = 0 := by rw [AddCircle.coe_period, nsmul_zero]
  change (((i : ℝ) + t : ℝ) : Circle) = (t : Circle)
  rw [AddCircle.coe_add, hi, zero_add]

private theorem nsmul_project (n : ℕ) (t : ℝ) :
    n • project t = project ((n : ℝ) * t) := by
  change n • (t : Circle) = (((n : ℝ) * t : ℝ) : Circle)
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]

private abbrev TourDomain (N : ℕ) := Fin N × Icc (0 : ℝ) 1

private def tourCoordinate (a : TourDomain N) : Circle :=
  project (((a.1.val : ℝ) + a.2.val) / N)

private def tourPoint (a : TourDomain N) : Space N := sheet a.1 (project a.2.val)

private theorem continuous_tourCoordinate : Continuous (tourCoordinate (N := N)) :=
  continuous_prod_of_discrete_left.mpr fun i => by
    change Continuous fun t : Icc (0 : ℝ) 1 => project (((i.val : ℝ) + t.val) / N)
    exact continuous_project.comp ((continuous_const.add continuous_subtype_val).div_const _)

private theorem continuous_tourPoint : Continuous (tourPoint (N := N)) :=
  continuous_prod_of_discrete_left.mpr fun i =>
    (continuous_sheet i).comp (continuous_project.comp continuous_subtype_val)

private def tourParameter (hN : 0 < N) (x : Circle) : TourDomain N := by
  let t := (N : ℝ) * coordinate 0 x
  have hx := coordinate_mem 0 x
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht : 0 ≤ t := mul_nonneg hN'.le hx.1
  have htN : t < (N : ℝ) := by
    dsimp [t]
    simpa only [zero_add, mul_one] using mul_lt_mul_of_pos_left hx.2 hN'
  exact ⟨⟨⌊t⌋₊, (Nat.floor_lt ht).mpr htN⟩,
    ⟨t - ⌊t⌋₊, sub_nonneg.mpr (Nat.floor_le ht),
      sub_le_iff_le_add.mpr (by simpa [add_comm] using (Nat.lt_floor_add_one t).le)⟩⟩

private theorem tourCoordinate_tourParameter (hN : 0 < N) (x : Circle) :
    tourCoordinate (tourParameter hN x) = x := by
  change project (((⌊(N : ℝ) * coordinate 0 x⌋₊ : ℕ) +
    ((N : ℝ) * coordinate 0 x - ⌊(N : ℝ) * coordinate 0 x⌋₊)) / N) = x
  rw [add_sub_cancel, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne'), project_coordinate]

private theorem nsmul_tourCoordinate (hN : 0 < N) (a : TourDomain N) :
    N • tourCoordinate a = project a.2.val := by
  rw [tourCoordinate, nsmul_project, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne'),
    project_nat_add]

private theorem tourPoint_eq (hN : 0 < N) {a b : TourDomain N}
    (h : tourCoordinate a = tourCoordinate b) : tourPoint a = tourPoint b := by
  have hcircle : project a.2.val = project b.2.val := by
    rw [← nsmul_tourCoordinate hN a, ← nsmul_tourCoordinate hN b, h]
  change sheet a.1 (project a.2.val) = sheet b.1 (project b.2.val)
  rw [← hcircle]
  by_cases ha : project a.2.val = 0
  · rw [ha, sheet_zero]
  · have ha1 : a.2.val < 1 := a.2.property.2.lt_of_ne (fun he => ha (he.symm ▸ project_one))
    have hb1 : b.2.val < 1 := b.2.property.2.lt_of_ne
      (fun he => ha (hcircle.trans (he.symm ▸ project_one)))
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hmem (z : TourDomain N) (hz : z.2.val < 1) :
        ((z.1.val : ℝ) + z.2.val) / (N : ℝ) ∈ Ico 0 (0 + 1) := by
      have hi : (z.1.val : ℝ) + 1 ≤ N := by exact_mod_cast z.1.isLt
      exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) z.2.property.1) hN'.le,
        (div_lt_iff₀ hN').mpr (by linarith)⟩
    have hreal := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem a ha1) (hmem b hb1)).mp h
    have hsum : (a.1.val : ℝ) + a.2.val = (b.1.val : ℝ) + b.2.val :=
      (div_left_inj' hN'.ne').mp hreal
    have hlabel : a.1 = b.1 := by
      apply Fin.ext
      rcases lt_trichotomy a.1.val b.1.val with hab | hab | hab
      · have hh : (a.1.val : ℝ) + 1 ≤ b.1.val := by exact_mod_cast hab
        linarith [b.2.property.1]
      · exact hab
      · have hh : (b.1.val : ℝ) + 1 ≤ a.1.val := by exact_mod_cast hab
        linarith [a.2.property.1]
    rw [hlabel]

/-- Traverse loop `i` as the coordinate runs from `i/N` to `(i+1)/N`. -/
def traverse (hN : 0 < N) (x : Circle) : Space N := tourPoint (tourParameter hN x)

/-- On the closed parameter interval of loop `i`, the tour follows that loop at speed `N`. -/
theorem traverse_project (hN : 0 < N) (i : Fin N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    traverse hN (project (((i.val : ℝ) + t) / N)) = sheet i (project t) := by
  let a : TourDomain N := (i, ⟨t, ht⟩)
  exact tourPoint_eq hN (tourCoordinate_tourParameter hN (tourCoordinate a))

/-- The closed interval pieces agree at their endpoints and descend continuously. -/
theorem continuous_traverse (hN : 0 < N) : Continuous (traverse hN) := by
  have hq : IsQuotientMap (tourCoordinate (N := N)) :=
    continuous_tourCoordinate.isClosedMap.isQuotientMap continuous_tourCoordinate
      (fun x => ⟨tourParameter hN x, tourCoordinate_tourParameter hN x⟩)
  refine hq.continuous_iff.mpr ?_
  exact continuous_tourPoint.congr fun a => (traverse_project hN a.1 a.2.property).symm

private theorem surjective_traverse (hN : 0 < N) : Surjective (traverse hN) := by
  intro p
  obtain ⟨i, hi⟩ := exists_sheet p
  let t := coordinate 0 (projection p)
  have ht := coordinate_mem 0 (projection p)
  let a : TourDomain N := ⟨i, t, ht.1, by simpa using ht.2.le⟩
  refine ⟨tourCoordinate a, ?_⟩
  exact (traverse_project hN i a.2.property).trans (by rwa [project_coordinate])

/-- Forgetting the loop after the tour is multiplication by `N` on the circle. -/
theorem projection_traverse (hN : 0 < N) (x : Circle) :
    projection (traverse hN x) = N • x := by
  let a := tourParameter hN x
  rw [← tourCoordinate_tourParameter hN x,
    show traverse hN (tourCoordinate a) = tourPoint a from
      traverse_project hN a.1 a.2.property, nsmul_tourCoordinate hN]
  rfl

/-- The bouquet map forgets the incoming label and then traverses all loops. -/
def bouquetMap (hN : 0 < N) : Space N → Space N := traverse hN ∘ projection

private theorem projection_semiconj (hN : 0 < N) :
    Semiconj projection (bouquetMap hN) (fun x : Circle => N • x) :=
  fun p => projection_traverse hN (projection p)

private theorem iterate_bouquetMap_succ (hN : 0 < N) (m : ℕ) (p : Space N) :
    (bouquetMap hN)^[m + 1] p = traverse hN ((N ^ m) • projection p) := by
  induction m with
  | zero => simp [bouquetMap]
  | succ m ih =>
    rw [iterate_succ_apply', ih]
    change traverse hN (projection (traverse hN _)) = _
    rw [projection_traverse, smul_smul, pow_succ']

private theorem exists_interval_in_projection {U : Set (Space N)} (hU : IsOpen U)
    (hne : U.Nonempty) : ∃ a b : ℝ, a < b ∧ project '' Icc a b ⊆ projection '' U := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨i, hi⟩ := exists_sheet p
  let x := coordinate 0 (projection p)
  have hx : x ∈ (sheet i ∘ project) ⁻¹' U := by
    change sheet i (project x) ∈ U
    rwa [project_coordinate, hi]
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp
    (hU.preimage ((continuous_sheet i).comp continuous_project)) x hx
  refine ⟨x, x + r / 2, by linarith, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hball : t ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  exact ⟨sheet i (project t), hsub hball, rfl⟩

private theorem topologically_exact {hN : 0 < N} (hN₂ : 2 ≤ N)
    (U : Set (Space N)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ k : ℕ, 0 < k ∧ (bouquetMap hN)^[k] '' U = univ := by
  obtain ⟨a, b, hab, hsub⟩ := exists_interval_in_projection hU hne
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (b - a)) hN'
  have hwide := (div_lt_iff₀ (sub_pos.mpr hab)).mp hm
  let K : ℝ := (N : ℝ) ^ m
  have hK : 0 < K := pow_pos (by linarith) _
  refine ⟨m + 1, by omega, eq_univ_of_forall fun q => ?_⟩
  obtain ⟨y, hy⟩ := surjective_traverse hN q
  let t := coordinate (K * a) y
  have ht : t ∈ Ico (K * a) (K * a + 1) := coordinate_mem (K * a) y
  have hab' : t / K ∈ Icc a b := by
    refine ⟨(le_div_iff₀ hK).mpr (by simpa [mul_comm] using ht.1), (div_le_iff₀ hK).mpr ?_⟩
    dsimp [K] at ht hwide ⊢
    linarith [ht.2]
  obtain ⟨p, hp, hp'⟩ := hsub ⟨t / K, hab', rfl⟩
  refine ⟨p, hp, ?_⟩
  rw [iterate_bouquetMap_succ, hp', nsmul_project, Nat.cast_pow]
  change traverse hN (project (K * (t / K))) = q
  rw [mul_div_cancel₀ _ hK.ne', project_coordinate, hy]

private theorem dist_nsmul_of_lt (hN : 0 < N) {x y : Circle}
    (h : dist x y < 1 / (2 * (N : ℝ))) :
    dist (N • x) (N • y) = (N : ℝ) * dist x y := by
  let u := coordinate (-1 / 2) (x - y)
  have hu : project u = x - y := project_coordinate _ _
  have huI : u ∈ Ico (-1 / 2) (-1 / 2 + 1) := coordinate_mem (-1 / 2) (x - y)
  have hsmall : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [huI.1], by linarith [huI.2]⟩
  have habs : dist x y = |u| := by
    rw [dist_eq_norm, ← hu]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by simpa using hsmall)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hlarge : |(N : ℝ) * u| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_mul, abs_of_nonneg hN'.le, ← habs, abs_one]
    have h' := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hN')).mp h
    linarith
  rw [dist_eq_norm, ← nsmul_sub, ← hu, nsmul_project]
  have hnorm := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hlarge
  simpa [project, abs_mul, abs_of_nonneg hN'.le, habs] using hnorm

private theorem circle_positivelyExpansive (hN : 2 ≤ N) :
    PositivelyExpansive (fun x : Circle => N • x) := by
  let g (x : Circle) := N • x
  let c : ℝ := 1 / (2 * N)
  have hN' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  refine ⟨c, by dsimp [c]; positivity, fun x y h => dist_eq_zero.mp ?_⟩
  have hgrowth (m : ℕ) :
      dist (g^[m] x) (g^[m] y) = (N : ℝ) ^ m * dist x y := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [iterate_succ_apply', iterate_succ_apply']
      change dist (N • g^[m] x) (N • g^[m] y) = _
      rw [dist_nsmul_of_lt (by omega) (h m), ih, pow_succ']
      ring
  by_contra hne
  have hd : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (c / dist x y) hN'
  exact (not_lt_of_ge ((div_lt_iff₀ hd).mp hm).le) (hgrowth m ▸ h m)

private theorem forwardBowenBound (hN : 0 < N) (hN₂ : 2 ≤ N) :
    ∃ ε > 0, ForwardBowenBound (bouquetMap hN) univ ε N := by
  obtain ⟨c, hc, hex⟩ := circle_positivelyExpansive hN₂
  refine ⟨c, hc, fun p _ => (Set.encard_mono (b := range (fun i => sheet i (projection p)))
    ?_).trans ?_⟩
  · intro q hq
    have he : projection p = projection q := hex _ _ fun n => by
      rw [← (projection_semiconj hN).iterate_right n p,
        ← (projection_semiconj hN).iterate_right n q]
      exact (le_max_left _ _).trans_lt (hq.2 n)
    obtain ⟨i, hi⟩ := exists_sheet q
    exact ⟨i, he.symm ▸ hi⟩
  · simpa only [← image_univ, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      using Set.encard_image_le (fun i : Fin N => sheet i (projection p)) univ

private theorem exists_small_fibre (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Circle, Injective (fun i : Fin N => sheet i x) ∧
      ∀ i j : Fin N, sheet j x ∈ ForwardBowen (bouquetMap hN) ε (sheet i x) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let t := min (1 / 2 : ℝ) (ε / (2 * N))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htmax : t ≤ 1 / 2 := min_le_left _ _
  have hd : dist (project t) 0 = t := by
    rw [← project_zero, project_dist_eq (by simpa [abs_of_pos ht] using htmax), Real.dist_eq]
    simp [abs_of_pos ht]
  have hx : project t ≠ 0 := by
    intro hz
    rw [hz, dist_self] at hd
    exact ht.ne' hd.symm
  refine ⟨project t, fun _ _ hij => sheet_label_eq hx hij, fun i j n => ?_⟩
  cases n with
  | zero =>
    change max (dist (project t) (project t))
      (dist ((i.val : ℝ) * dist (project t) 0) ((j.val : ℝ) * dist (project t) 0)) < ε
    rw [dist_self, max_eq_right dist_nonneg, Real.dist_eq, hd, ← sub_mul,
      abs_mul, abs_of_pos ht]
    have hi : (i.val : ℝ) ≤ N := Nat.cast_le.mpr i.isLt.le
    have hj : (j.val : ℝ) ≤ N := Nat.cast_le.mpr j.isLt.le
    have hgap : |(i.val : ℝ) - (j.val : ℝ)| ≤ N :=
      abs_sub_le_iff.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) j.val],
        by linarith [Nat.cast_nonneg (α := ℝ) i.val]⟩
    calc
      _ ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hgap ht.le
      _ ≤ (N : ℝ) * (ε / (2 * N)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hN'.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  | succ n =>
    rw [iterate_bouquetMap_succ, iterate_bouquetMap_succ, projection_sheet, projection_sheet,
      dist_self]
    exact hε

private theorem no_smaller_bound (hN : 0 < N) (hN₂ : 2 ≤ N) :
    ∀ ε > 0, ¬ ForwardBowenBound (bouquetMap hN) univ ε (N - 1) := by
  intro ε hε hb
  obtain ⟨x, hi, hclose⟩ := exists_small_fibre hN hε
  let i : Fin N := ⟨0, hN⟩
  have hcard : (N : ℕ∞) ≤ (univ ∩ ForwardBowen (bouquetMap hN) ε (sheet i x)).encard :=
    (Set.le_encard_iff_exists_fin_injective _ N).mpr
      ⟨fun j => sheet j x, fun j => ⟨mem_univ _, hclose i j⟩, hi⟩
  have hbad : N ≤ N - 1 := by exact_mod_cast hcard.trans (hb _ (mem_univ _))
  omega

/-- For every `N ≥ 2`, the explicit bouquet map is a continuous surjection,
is topologically exact, and has least positive expansivity order `N`. -/
theorem exact_order {N : ℕ} (hN : 2 ≤ N) :
    let F := bouquetMap (show 0 < N by omega)
    CompactSpace (Space N) ∧ Continuous F ∧ Surjective F ∧
      (∀ U : Set (Space N), IsOpen U → U.Nonempty → ∃ k : ℕ, 0 < k ∧ F^[k] '' U = univ) ∧
      (∃ ε > 0, ForwardBowenBound F univ ε N) ∧
      (∀ ε > 0, ¬ ForwardBowenBound F univ ε (N - 1)) := by
  let hpos : 0 < N := by omega
  exact ⟨compactSpace_space N, (continuous_traverse hpos).comp continuous_projection,
    (surjective_traverse hpos).comp (fun x => ⟨sheet ⟨0, hpos⟩ x, rfl⟩),
    fun U => topologically_exact hN U, forwardBowenBound hpos hN, no_smaller_bound hpos hN⟩

end D5.S1.Dynamics.Shadowing.BouquetExactExpansivity
