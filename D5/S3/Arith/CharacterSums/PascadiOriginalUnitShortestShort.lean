/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiOriginalUnitShortestShort
   mirror-E: none(waiver:open-original-total-count)
   anchors: []
   utility: none
   digest: The short unit-vector charts count actual original tuples in all physical scales. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalChartPieces

/-! Original parameters and endpoints are counted together in each actual
short unit-vector lattice, then summed over the physical dyadic scales. -/

open scoped BigOperators

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem short_basis_boundary_lower {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H s₀ : ℝ} (hH : 0 < H) (hHsq : H^2 = X*Y)
    (harea : (p : ℝ)^3 ≤ X*Y) (hs₀ : 0 < s₀)
    (B : ReducedMiddleBasis (p^3) t w X Y)
    (hlow : s₀^2 ≤ weightedSq X Y B.R)
    (hshort : H^2*weightedSq X Y B.R ≤ (p : ℝ)^6) : 1 ≤ H/s₀ := by
  have hc : 0 < (p : ℝ)^3 := by exact_mod_cast pow_pos hp.pos 3
  have hbound : (H*s₀)^2 ≤ ((p : ℝ)^3)^2 := by
    have hh := mul_le_mul_of_nonneg_left hlow (sq_nonneg H)
    nlinarith
  have hHs : H*s₀ ≤ (p : ℝ)^3 :=
    (sq_le_sq₀ (by positivity) hc.le).mp hbound
  have hHlower : s₀ ≤ H := by
    have hh : H*s₀ ≤ H*H := by nlinarith [harea]
    exact (mul_le_mul_iff_right₀ hH).mp hh
  exact (le_div_iff₀ hs₀).mpr (by simpa using hHlower)

private theorem short_basis_box_section_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H s₀ : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y) (harea : (p : ℝ)^3 ≤ X*Y)
    (hs₀ : 0 < s₀) (B : ReducedMiddleBasis (p^3) t w X Y)
    (hlow : s₀^2 ≤ weightedSq X Y B.R)
    (hshort : H^2*weightedSq X Y B.R ≤ (p : ℝ)^6)
    (F : Finset Coordinate)
    (hmem : ∀ z ∈ F, z ∈ middleLattice (p^3) t w)
    (hbox : ∀ z ∈ F, z ∈ literalBox X Y) : (F.card : ℝ) ≤ 48*(H/s₀) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hc : 0 < (p : ℝ)^3 := by positivity
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hσ : 0 < σ := Real.sqrt_pos.mpr
    (weightedSq_pos hX hY (B.first_ne_zero (pow_pos hp.pos _)))
  have hσsq : σ^2 = weightedSq X Y B.R :=
    Real.sq_sqrt (weightedSq_nonneg hX hY _)
  have hσlow : s₀ ≤ σ := (sq_le_sq₀ hs₀.le hσ.le).mp (by simpa only [hσsq] using hlow)
  have hboundary : H/σ ≤ H/s₀ := div_le_div_of_nonneg_left hH.le hs₀ hσlow
  have hbound : (H*s₀)^2 ≤ ((p : ℝ)^3)^2 := by
    have hh := mul_le_mul_of_nonneg_left hlow (sq_nonneg H)
    nlinarith
  have hHs : H*s₀ ≤ (p : ℝ)^3 :=
    (sq_le_sq₀ (by positivity) hc.le).mp hbound
  have hvolume : X*Y/(p : ℝ)^3 ≤ H/s₀ := by
    apply (div_le_div_iff₀ hc hs₀).mpr
    have hh := mul_le_mul_of_nonneg_left hHs hH.le
    nlinarith [hHsq]
  have hone := short_basis_boundary_lower hp hH hHsq harea hs₀ B hlow hshort
  have hF := actual_middle_box_section_count B (pow_pos hp.pos _) hX hY H hH hHsq F hmem hbox
  dsimp only at hF
  push_cast at hF
  change (F.card : ℝ) ≤ 16*(1+H/σ+X*Y/(p : ℝ)^3) at hF
  linarith

private theorem common_shortest_rows_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H s₀ : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y) (harea : (p : ℝ)^3 ≤ X*Y)
    (hXsmall : 2*X < (p^2 : ℕ)) (hYsmall : 2*Y < (p^3 : ℕ))
    (hs₀ : 0 < s₀) (B : ReducedMiddleBasis (p^3) t w X Y)
    (hlow : s₀^2 ≤ weightedSq X Y B.R)
    (hshort : H^2*weightedSq X Y B.R ≤ (p : ℝ)^6)
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (S : Finset ReturnRows)
    (hbox : ∀ h ∈ S, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ S, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ S, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3)))
    (hshared : ∀ h ∈ S, middleLattice (p^3) (h.2 2) (h.1 2) =
      middleLattice (p^3) t w) : (S.card : ℝ) ≤ 4656*(H/s₀)^2 := by
  classical
  letI : NeZero (p ^ 3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let points (h : ReturnRows) : Finset Coordinate :=
    {originalMiddle h, (originalEndpoints h).1, (originalEndpoints h).2}
  let F := S.biUnion points
  let P := S.image originalMiddle
  have hpnt (h : ReturnRows) (hh : h ∈ S) (z : Coordinate) (hz : z ∈ points h) :
      z ∈ middleLattice (p ^ 3) t w ∧ z ∈ literalBox X Y := by
    have heq := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp (hword h hh)
    have hmid : originalMiddle h ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      simp only [originalMiddle, middleLattice, Set.mem_ofPred_eq, Prod.fst, Prod.snd,
        mul_comm, sub_self, dvd_zero]
    have hfirst : (originalEndpoints h).1 ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [originalEndpoints, Int.cast_sub, Int.cast_mul] using
        sub_eq_zero.mpr heq.2.2.1
    have hsecond : (originalEndpoints h).2 ∈ middleLattice (p ^ 3) (h.2 2) (h.1 2) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [originalEndpoints, Int.cast_sub, Int.cast_mul] using
        sub_eq_zero.mpr heq.2.2.2
    simp only [points, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨hshared h hh ▸ hmid, hbox h hh 2⟩
    · exact ⟨hshared h hh ▸ hfirst, hbox h hh 0⟩
    · exact ⟨hshared h hh ▸ hsecond, hbox h hh 1⟩
  have hF (z : Coordinate) (hz : z ∈ F) :
      z ∈ middleLattice (p ^ 3) t w ∧ z ∈ literalBox X Y := by
    obtain ⟨h, hh, hz⟩ := Finset.mem_biUnion.mp hz
    exact hpnt h hh z hz
  have hFin (h : ReturnRows) (hh : h ∈ S) :
      originalMiddle h ∈ F ∧ (originalEndpoints h).1 ∈ F ∧ (originalEndpoints h).2 ∈ F := by
    constructor
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp only [points, Finset.mem_insert, true_or]⟩
    constructor
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp [points]⟩
    · exact Finset.mem_biUnion.mpr ⟨h, hh, by simp [points]⟩
  have hFcount : (F.card : ℝ) ≤ 48*(H/s₀) :=
    short_basis_box_section_count hp hX hY hH hHsq harea hs₀ B hlow hshort F
      (fun z hz => (hF z hz).1) (fun z hz => (hF z hz).2)
  have hPcount : P.card ≤ F.card := Finset.card_le_card (by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hz
    exact (hFin h hh).1)
  have hfiber (wt : Coordinate) (hwt : wt ∈ P) :
      (S.filter (fun h => originalMiddle h = wt)).card ≤ 2*F.card+1 := by
    obtain ⟨h₀, hh₀, he₀⟩ := Finset.mem_image.mp hwt
    let A := S.filter fun h => originalMiddle h = wt
    let E := A.image originalEndpoints
    have hm (h : ReturnRows) (hh : h ∈ A) : h ∈ S ∧
        h.1 2 = h₀.1 2 ∧ h.2 2 = h₀.2 2 := by
      have ha := Finset.mem_filter.mp hh
      exact ⟨ha.1, (congrArg Prod.fst ha.2).trans (congrArg Prod.fst he₀).symm,
        (congrArg Prod.snd ha.2).trans (congrArg Prod.snd he₀).symm⟩
    have hinj : Set.InjOn originalEndpoints (A : Set ReturnRows) := by
      intro h hh h' hh' he
      have hb := hm h hh
      have hb' := hm h' hh'
      apply Prod.ext <;> funext i <;> fin_cases i
      · exact congrArg (fun e : Endpoint => e.1.1) he
      · exact congrArg (fun e : Endpoint => e.2.1) he
      · exact hb.2.1.trans hb'.2.1.symm
      · exact congrArg (fun e : Endpoint => e.1.2) he
      · exact congrArg (fun e : Endpoint => e.2.2) he
      · exact hb.2.2.trans hb'.2.2.symm
    have hsub : E ⊆ (F.product F).filter fun e => sixReturnWord a₁ a₂
        (e.1.1 : ZMod (p ^ 3)) (h₀.2 2) e.2.1 e.1.2 (h₀.1 2) e.2.2 =
          scalarReturn (-1) := by
      intro e he
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hs, hwm, htm⟩ := hm h hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(hFin h hs).2.1, (hFin h hs).2.2⟩, ?_⟩
      simpa only [originalEndpoints, hwm, htm] using hword h hs
    have helem := actual_endpoint_pair_elementary_count hp hXsmall hYsmall
      a₁ a₂ ha₁ ha₂ (hunit h₀ hh₀).2 (hunit h₀ hh₀).1 F (by
        intro z hz
        rw [hshared h₀ hh₀]
        exact (hF z hz).1) (fun z hz => (hF z hz).2)
    calc
      A.card = E.card := by simp only [E, Finset.card_image_of_injOn hinj]
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ 2*F.card+1 := helem
  have hcount : (S.card : ℝ) =
      ∑ wt ∈ P, ((S.filter (fun h => originalMiddle h = wt)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image originalMiddle S
  have hA : 1 ≤ H/s₀ := short_basis_boundary_lower hp hH hHsq harea hs₀ B hlow hshort
  have hpc : (P.card : ℝ) ≤ 48*(H/s₀) := by
    have hpc' : (P.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hPcount
    exact hpc'.trans (by simpa only [mul_div_assoc] using hFcount)
  have hec : 2*(F.card : ℝ)+1 ≤ 97*(H/s₀) := by
    have hf : (F.card : ℝ) ≤ 48*(H/s₀) := by
      simpa only [mul_div_assoc] using hFcount
    linarith
  calc
    (S.card : ℝ) = ∑ wt ∈ P, ((S.filter (fun h => originalMiddle h = wt)).card : ℝ) := hcount
    _ ≤ ∑ _wt ∈ P, (2*(F.card : ℝ)+1) := Finset.sum_le_sum (by
      intro wt hwt
      exact_mod_cast hfiber wt hwt)
    _ = (P.card : ℝ)*(2*(F.card : ℝ)+1) := by simp; ring
    _ ≤ (48*(H/s₀))*(97*(H/s₀)) :=
      mul_le_mul hpc hec (by positivity) (by positivity)
    _ = 4656*(H/s₀) ^ 2 := by ring

private theorem unit_middle_basis_nonaxis {c : ℕ} [Nontrivial (ZMod c)]
    {t w : ℤ} {X Y : ℝ} (B : ReducedMiddleBasis c t w X Y)
    (ht : IsUnit (t : ZMod c)) (hr : IsUnit (B.R.1 : ZMod c)) :
    B.R.1 ≠ 0 ∧ B.R.2 ≠ 0 := by
  constructor
  · intro hz
    exact hr.ne_zero (by simp only [hz, Int.cast_zero])
  · intro hz
    have hm := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr B.memR
    push_cast at hm
    apply (ht.mul hr).ne_zero
    simpa only [hz, Int.cast_zero, mul_zero, zero_sub, neg_eq_zero] using hm

private theorem unit_shortest_short_scale_count {p : ℕ} (hp : p.Prime)
    {X Y H s₀ : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y) (harea : (p : ℝ)^3 ≤ X*Y)
    (hXsmall : 2*X < (p^2 : ℕ)) (hYsmall : 2*Y < (p^3 : ℕ))
    (hs₀ : 0 < s₀) (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (T : Finset ReturnRows) (R : ReturnRows → Coordinate)
    (hbox : ∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3)))
    (hred : ∀ h ∈ T, ∃ B : ReducedMiddleBasis (p^3) (h.2 2) (h.1 2) X Y, B.R = R h)
    (hr : ∀ h ∈ T, IsUnit ((R h).1 : ZMod (p^3)))
    (hlow : ∀ h ∈ T, s₀^2 ≤ weightedSq X Y (R h))
    (hhigh : ∀ h ∈ T, weightedSq X Y (R h) ≤ 4*s₀^2)
    (hshort : ∀ h ∈ T, H^2*weightedSq X Y (R h) ≤ (p : ℝ)^6) :
    (T.card : ℝ) ≤ 74496*(X*Y) := by
  classical
  letI : Fact (1 < p^3) := ⟨one_lt_pow₀ hp.one_lt (by decide : 3 ≠ 0)⟩
  let K := T.image R
  have hK : (K.card : ℝ) ≤ 16*s₀^2 := by
    have hh := nonaxis_short_vector_candidates_count hX hY hH hHsq
      (show 0 ≤ 2*s₀ by positivity) K (by
        intro u hu
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨B, hBR⟩ := hred h hh
        have hru : IsUnit (B.R.1 : ZMod (p^3)) := by rw [hBR]; exact hr h hh
        simpa only [hBR] using unit_middle_basis_nonaxis B (hunit h hh).2 hru)
      (by
        intro u hu
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hu
        nlinarith [hhigh h hh])
    nlinarith
  have hfiber (u : Coordinate) (hu : u ∈ K) :
      ((T.filter (fun h => R h = u)).card : ℝ) ≤ 4656*(H/s₀)^2 := by
    obtain ⟨h₀, hh₀, he₀⟩ := Finset.mem_image.mp hu
    obtain ⟨B₀, hB₀⟩ := hred h₀ hh₀
    let S := T.filter fun h => R h = u
    have hS (h : ReturnRows) (hh : h ∈ S) : h ∈ T ∧ R h = R h₀ := by
      exact ⟨(Finset.mem_filter.mp hh).1, (Finset.mem_filter.mp hh).2.trans he₀.symm⟩
    apply common_shortest_rows_count hp hX hY hH hHsq harea hXsmall hYsmall hs₀ B₀
      (by simpa only [hB₀] using hlow h₀ hh₀)
      (by simpa only [hB₀] using hshort h₀ hh₀) a₁ a₂ ha₁ ha₂ S
      (fun h hh => hbox h (hS h hh).1) (fun h hh => hword h (hS h hh).1)
      (fun h hh => hunit h (hS h hh).1)
    intro h hh
    obtain ⟨B, hBR⟩ := hred h (hS h hh).1
    have hm : R h₀ ∈ middleLattice (p^3) (h.2 2) (h.1 2) := by
      rw [← (hS h hh).2, ← hBR]
      exact B.memR
    have hm₀ : R h₀ ∈ middleLattice (p^3) (h₀.2 2) (h₀.1 2) := by
      rw [← hB₀]
      exact B₀.memR
    exact (middleLattice_eq_of_unit_vector (hunit h (hS h hh).1).1
      (R h₀) (hr h₀ hh₀) hm).trans
      (middleLattice_eq_of_unit_vector (hunit h₀ hh₀).1 (R h₀) (hr h₀ hh₀) hm₀).symm
  have hcount : (T.card : ℝ) = ∑ u ∈ K,
      ((T.filter (fun h => R h = u)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image R T
  calc
    _ = ∑ u ∈ K, ((T.filter (fun h => R h = u)).card : ℝ) := hcount
    _ ≤ ∑ _u ∈ K, 4656*(H/s₀)^2 := Finset.sum_le_sum hfiber
    _ = (K.card : ℝ)*(4656*(H/s₀)^2) := by simp
    _ ≤ (16*s₀^2)*(4656*(H/s₀)^2) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = 74496*(X*Y) := by
      field_simp [hs₀.ne']
      nlinarith [hHsq]

/-- All actual short unit-vector charts contribute O(XY log(2p)). The
dyadic scales, common lattices, original parameters and endpoint injections
are constructed from the original six-row tuples themselves. -/
theorem actual_unit_shortest_short_tuple_count {p : ℕ} (hp : p.Prime)
    {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y) (harea : (p : ℝ)^3 ≤ X*Y)
    (hXsmall : 2*X < (p^2 : ℕ)) (hYsmall : 2*Y < (p^3 : ℕ))
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (T : Finset ReturnRows) (R : ReturnRows → Coordinate)
    (hbox : ∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y)
    (hword : ∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
      (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1))
    (hunit : ∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3)))
    (hred : ∀ h ∈ T, ∃ B : ReducedMiddleBasis (p^3) (h.2 2) (h.1 2) X Y, B.R = R h)
    (hr : ∀ h ∈ T, IsUnit ((R h).1 : ZMod (p^3)))
    (hshort : ∀ h ∈ T, H^2*weightedSq X Y (R h) ≤ (p : ℝ)^6) :
    (T.card : ℝ) ≤ 148992*(X*Y)*(1+Real.log (2*p)/Real.log 2) := by
  classical
  letI : Fact (1 < p^3) := ⟨one_lt_pow₀ hp.one_lt (by decide : 3 ≠ 0)⟩
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  let Q := fun h => weightedSq X Y (R h)
  let U : ℝ := 2*(p : ℝ)^2
  have hU : 1 ≤ U := by dsimp [U]; nlinarith
  obtain ⟨N, hNlow, hNhigh⟩ := exists_nat_pow_near hU (by norm_num : (1 : ℝ) < 2)
  let P := fun k h => ((2 : ℝ)^k)^2 ≤ Q h ∧ Q h < 4*((2 : ℝ)^k)^2
  let S := fun k => T.filter (P k)
  have hnorm (h : ReturnRows) (hh : h ∈ T) :
      1 ≤ Real.sqrt (Q h) ∧ Real.sqrt (Q h) ≤ U := by
    obtain ⟨B, hBR⟩ := hred h hh
    have hru : IsUnit (B.R.1 : ZMod (p^3)) := by rw [hBR]; exact hr h hh
    obtain ⟨h₁, h₂⟩ := unit_middle_basis_nonaxis B (hunit h hh).2 hru
    have hab (z : ℤ) (hz : z ≠ 0) : 1 ≤ |(z : ℝ)| := by
      have hi : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hz; omega
      exact_mod_cast hi
    have hprod : 1 ≤ |(B.R.1 : ℝ)| * |(B.R.2 : ℝ)| := by
      simpa only [one_mul] using mul_le_mul (hab _ h₁) (hab _ h₂)
        (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg _)
    have hQ : Q h < 2*(p : ℝ)^3 := by
      simpa only [Q, hBR, Nat.cast_pow] using (B.reduction_bounds (pow_pos hp.pos _) hX hY).2.1
    constructor
    · apply Real.le_sqrt_of_sq_le
      have hh := two_abs_product_le_weightedSq hX hY B.R
      dsimp [Q]
      rw [← hBR]
      nlinarith
    · apply Real.sqrt_le_iff.mpr
      refine ⟨by dsimp [U]; positivity, ?_⟩
      have hp34 : (p : ℝ)^3 ≤ (p : ℝ)^4 := pow_le_pow_right₀ hp1 (by decide : 3 ≤ 4)
      dsimp [U]
      nlinarith [pow_nonneg hpR.le 4]
  have hcover : ∀ h ∈ T, h ∈ (Finset.range (N+1)).biUnion S := by
    intro h hh
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near (hnorm h hh).1
      (by norm_num : (1 : ℝ) < 2)
    have hk : k < N+1 := by
      apply (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      exact hklo.trans_lt ((hnorm h hh).2.trans_lt hNhigh)
    have hs : P k h := by
      have hsq := Real.sq_sqrt (weightedSq_nonneg hX hY (R h))
      have hlo := (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg (Q h))).mpr hklo
      have hhi := (sq_lt_sq₀ (Real.sqrt_nonneg (Q h)) (by positivity)).mpr hkhi
      rw [show (2 : ℝ)^(k+1) = (2 : ℝ)^k*2 by rw [pow_succ]] at hhi
      change (Real.sqrt (Q h))^2 = Q h at hsq
      constructor <;> nlinarith
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, Finset.mem_filter.mpr ⟨hh, hs⟩⟩
  have hscale (k : ℕ) : ((S k).card : ℝ) ≤ 74496*(X*Y) := by
    have hrestrict {A : ReturnRows → Prop} (ha : ∀ h ∈ T, A h) : ∀ h ∈ S k, A h :=
      fun h hh => ha h (Finset.mem_filter.mp hh).1
    apply unit_shortest_short_scale_count hp hX hY hH hHsq harea hXsmall hYsmall
      (by positivity : 0 < (2 : ℝ)^k) a₁ a₂ ha₁ ha₂ (S k) R
      (hrestrict hbox) (hrestrict hword) (hrestrict hunit) (hrestrict hred) (hrestrict hr)
      (fun h hh => (Finset.mem_filter.mp hh).2.1)
      (fun h hh => (Finset.mem_filter.mp hh).2.2.le) (hrestrict hshort)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlogN : (N : ℝ)*Real.log 2 ≤ Real.log 2+2*Real.log (p : ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (2 : ℝ)^N) hNlow
    simpa only [Real.log_pow, U, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (pow_ne_zero 2 hpR.ne'), Real.log_pow, Nat.cast_ofNat] using hh
  have hNcount : ((N+1 : ℕ) : ℝ) ≤ 2*(1+Real.log (2*p)/Real.log 2) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpR.ne']
    apply (mul_le_mul_iff_of_pos_right hlog2).mp
    push_cast
    field_simp
    nlinarith
  have hcard : T.card ≤ ∑ k ∈ Finset.range (N+1), (S k).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  calc
    (T.card : ℝ) ≤ ∑ k ∈ Finset.range (N+1), ((S k).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _k ∈ Finset.range (N+1), 74496*(X*Y) := Finset.sum_le_sum fun k _ => hscale k
    _ = ((N+1 : ℕ) : ℝ)*(74496*(X*Y)) := by simp
    _ ≤ (2*(1+Real.log (2*p)/Real.log 2))*(74496*(X*Y)) :=
      mul_le_mul_of_nonneg_right hNcount (by positivity)
    _ = 148992*(X*Y)*(1+Real.log (2*p)/Real.log 2) := by ring

end
end D5.S3.Arith.CharacterSums.Original
