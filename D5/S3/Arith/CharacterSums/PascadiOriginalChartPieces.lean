/- GID: D5/S3/Arith/CharacterSums/PascadiOriginalChartPieces
   generality: G
   mirror-B: none(waiver:removed-original-unit-chart-pieces)
   mirror-E: none(waiver:removed-original-unit-chart-pieces)
   anchors: []
   utility: none
   digest: Actual original parameter counts for the removed unit-chart pieces. -/

import D5.S3.Arith.CharacterSums.PascadiOriginalElementaryFibers
import D5.S3.Arith.CharacterSums.PascadiOriginalWeightAverage
import D5.S3.Arith.CharacterSums.PascadiModularZeroPartners

/-! The long nonunit-right-side contribution is counted in original integer
parameters and physical endpoint sections, without additional slope lifts. -/

namespace D5.S3.Arith.CharacterSums.Original

noncomputable section

private theorem fixed_residue_product_values {p : ℕ} (hp : p.Prime)
    {A : ℝ} (hA : 0 ≤ A) (g : ZMod p) (hg : IsUnit g)
    (s : Finset ℤ) (hb : ∀ n ∈ s, |(n : ℝ)| ≤ A)
    (he : ∀ n ∈ s, 1+g*(n : ZMod p) = 0) :
    (s.card : ℝ) ≤ 1+4*A/p := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hs
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hdiv (n : ℤ) (hn : n ∈ s) : (p : ℤ) ∣ n-n₀ := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      apply hg.mul_left_cancel
      have h₁ := he n hn
      have h₂ := he n₀ hn₀
      linear_combination h₁-h₂
    let code (n : ℤ) := (n-n₀)/(p : ℤ)
    have hcode (n : ℤ) (hn : n ∈ s) : (p : ℤ)*code n = n-n₀ := by
      simpa only [code, mul_comm] using Int.ediv_mul_cancel (hdiv n hn)
    let K : ℝ := 2*A/p
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hc (n : ℤ) (hn : n ∈ s) : |(code n : ℝ)| ≤ K := by
      have hx : (p : ℝ)*(code n : ℝ) = (n : ℝ)-n₀ := by
        exact_mod_cast hcode n hn
      have hh : |(n : ℝ)-(n₀ : ℝ)| ≤ 2*A :=
        (abs_sub _ _).trans (by linarith [hb n hn, hb n₀ hn₀])
      rw [← hx, abs_mul, abs_of_pos hpR] at hh
      exact (le_div_iff₀ hpR).mpr (by simpa only [mul_comm] using hh)
    have hcard : s.card ≤ (Finset.Icc (-⌊K⌋) ⌊K⌋).card := by
      apply Finset.card_le_card_of_injOn code
      · intro n hn
        have hu := Int.le_floor.mpr (abs_le.mp (hc n hn)).2
        have hl : -code n ≤ ⌊K⌋ := Int.le_floor.mpr (by
          push_cast
          linarith [abs_le.mp (hc n hn)])
        exact Finset.mem_Icc.mpr ⟨by omega, hu⟩
      · intro n hn m hm hnm
        have h₁ := hcode n hn
        have h₂ := hcode m hm
        rw [hnm] at h₁
        omega
    have hfloor : 0 ≤ ⌊K⌋ := Int.floor_nonneg.mpr hK
    have hinterval : ((Finset.Icc (-⌊K⌋) ⌊K⌋).card : ℝ) =
        2*(⌊K⌋ : ℝ)+1 := by
      have h := Int.card_Icc_of_le (a := -⌊K⌋) (b := ⌊K⌋) (by omega)
      have h' : ((Finset.Icc (-⌊K⌋) ⌊K⌋).card : ℝ) =
          (⌊K⌋ : ℝ)+1-(-⌊K⌋ : ℤ) := by exact_mod_cast h
      push_cast at h'
      linarith
    calc
      (s.card : ℝ) ≤ ((Finset.Icc (-⌊K⌋) ⌊K⌋).card : ℝ) := by exact_mod_cast hcard
      _ = 2*(⌊K⌋ : ℝ)+1 := hinterval
      _ ≤ 2*K+1 := by linarith [Int.floor_le K]
      _ = 1+4*A/p := by dsimp [K]; ring
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The nonunit-right-side middle parameters are counted as original integer
factorizations of their product, without an independent slope lift. -/
theorem actual_nonunit_rhs_parameter_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y : ℝ),
      0 < X → 0 < Y → X*Y ≤ (p : ℝ)^4 →
      ∀ (g : ZMod p), IsUnit g → ∀ s : Finset Coordinate,
      (∀ wt ∈ s, wt ∈ literalBox X Y) →
      (∀ wt ∈ s, 1+g*(wt.1 : ZMod p)*(wt.2 : ZMod p) = 0) →
      (s.card : ℝ) ≤ C*(p : ℝ)^ε*(1+X*Y/p) := by
  obtain ⟨C, hC, hdiv⟩ := signed_divisors_antidiag_subpower (ε/4) (by positivity)
  refine ⟨4*C, by positivity, ?_⟩
  intro p hp X Y hX hY harea g hg s hbox he
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let vals := s.image (fun wt => wt.1*wt.2)
  have hval (n : ℤ) (hn : n ∈ vals) :
      |(n : ℝ)| ≤ X*Y ∧ 1+g*(n : ZMod p) = 0 := by
    obtain ⟨wt, hwt, rfl⟩ := Finset.mem_image.mp hn
    have hb := hbox wt hwt
    constructor
    · simpa only [Int.cast_mul, abs_mul] using
        mul_le_mul hb.1 hb.2 (abs_nonneg _) hX.le
    · simpa only [Int.cast_mul, mul_assoc] using he wt hwt
  have hn0 (n : ℤ) (hn : n ∈ vals) : n ≠ 0 := by
    intro hz
    have h := (hval n hn).2
    simp [hz] at h
  have hvals : (vals.card : ℝ) ≤ 1+4*(X*Y)/p :=
    fixed_residue_product_values hp (mul_pos hX hY).le g hg vals
      (fun n hn => (hval n hn).1) (fun n hn => (hval n hn).2)
  have hfiber (n : ℤ) (hn : n ∈ vals) :
      ((s.filter (fun wt => wt.1*wt.2=n)).card : ℝ) ≤ C*(p : ℝ)^ε := by
    have hc : (s.filter (fun wt => wt.1*wt.2=n)).card ≤
        (Int.divisorsAntidiag n).card := by
      apply Finset.card_le_card_of_injOn (fun wt : Coordinate => wt)
      · intro wt hwt
        exact Int.mem_divisorsAntidiag.mpr ⟨(Finset.mem_filter.mp hwt).2, hn0 n hn⟩
      · intro _ _ _ _ h
        exact h
    calc
      ((s.filter (fun wt => wt.1*wt.2=n)).card : ℝ) ≤
          ((Int.divisorsAntidiag n).card : ℝ) := by exact_mod_cast hc
      _ ≤ C*(n.natAbs : ℝ)^(ε/4) := hdiv n (hn0 n hn)
      _ ≤ C*((p : ℝ)^4)^(ε/4) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
        simpa only [Nat.cast_natAbs, Int.cast_abs] using (hval n hn).1.trans harea
      _ = C*(p : ℝ)^ε := by
        rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (p : ℝ)) 4 (ε/4)]
        congr 2
        ring
  have hcount : (s.card : ℝ) =
      ∑ n ∈ vals, ((s.filter (fun wt => wt.1*wt.2=n)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun wt : Coordinate => wt.1*wt.2) s
  calc
    (s.card : ℝ) = ∑ n ∈ vals, ((s.filter (fun wt => wt.1*wt.2=n)).card : ℝ) := hcount
    _ ≤ ∑ _n ∈ vals, C*(p : ℝ)^ε := Finset.sum_le_sum hfiber
    _ = (vals.card : ℝ)*(C*(p : ℝ)^ε) := by simp
    _ ≤ (1+4*(X*Y)/p)*(C*(p : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hvals (by positivity)
    _ ≤ (4*C)*(p : ℝ)^ε*(1+X*Y/p) := by
      calc
        _ = (C*(p : ℝ)^ε)*(1+4*(X*Y)/p) := by ring
        _ ≤ (C*(p : ℝ)^ε)*(4*(1+X*Y/p)) :=
          mul_le_mul_of_nonneg_left (by ring_nf; linarith) (by positivity)
        _ = _ := by ring

private theorem long_actual_endpoint_pair_count {p : ℕ} (hp : p.Prime)
    {t w : ℤ} {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 < H) (hHsq : H^2 = X*Y)
    (harea : (p : ℝ)^3 ≤ X*Y)
    (hXsmall : 2*X < (p^2 : ℕ)) (hYsmall : 2*Y < (p^3 : ℕ))
    (a₁ a₂ : ZMod (p^3)) (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (ht : IsUnit (t : ZMod (p^3))) (hw : IsUnit (w : ZMod (p^3)))
    (B : ReducedMiddleBasis (p^3) t w X Y)
    (hlong : (p : ℝ)^3 ≤ H*Real.sqrt (weightedSq X Y B.R))
    (F : Finset Coordinate)
    (hmem : ∀ z ∈ F, z ∈ middleLattice (p^3) t w)
    (hbox : ∀ z ∈ F, z ∈ literalBox X Y) :
    (((F.product F).filter fun e => sixReturnWord a₁ a₂
      (e.1.1 : ZMod (p^3)) (t : ZMod (p^3)) e.2.1 e.1.2 w e.2.2 =
        scalarReturn (-1)).card : ℝ) ≤ 97*(X*Y)/(p : ℝ)^3 := by
  let σ := Real.sqrt (weightedSq X Y B.R)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hσ : 0 < σ := Real.sqrt_pos.mpr
    (weightedSq_pos hX hY (B.first_ne_zero (pow_pos hp.pos _)))
  have hboundary : H/σ ≤ (X*Y)/(p : ℝ)^3 := by
    apply (div_le_div_iff₀ hσ (by positivity : 0 < (p : ℝ)^3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlong hH.le]
  have hvolume : 1 ≤ (X*Y)/(p : ℝ)^3 :=
    (le_div_iff₀ (by positivity : 0 < (p : ℝ)^3)).mpr (by simpa using harea)
  have hF := actual_middle_box_section_count B (pow_pos hp.pos _) hX hY H hH hHsq F hmem hbox
  have hFR : (F.card : ℝ) ≤ 48*((X*Y)/(p : ℝ)^3) := by
    dsimp only at hF
    push_cast at hF
    change (F.card : ℝ) ≤ 16*(1+H/σ+(X*Y)/(p : ℝ)^3) at hF
    linarith
  have he := actual_endpoint_pair_elementary_count hp hXsmall hYsmall
    a₁ a₂ ha₁ ha₂ ht hw F hmem hbox
  have heR : (((F.product F).filter fun e => sixReturnWord a₁ a₂
      (e.1.1 : ZMod (p^3)) (t : ZMod (p^3)) e.2.1 e.1.2 w e.2.2 =
        scalarReturn (-1)).card : ℝ) ≤ 2*(F.card : ℝ)+1 := by exact_mod_cast he
  calc
    _ ≤ 2*(F.card : ℝ)+1 := heR
    _ ≤ 97*((X*Y)/(p : ℝ)^3) := by linarith
    _ = 97*(X*Y)/(p : ℝ)^3 := by ring

def originalMiddle (h : ReturnRows) : Coordinate := (h.1 2, h.2 2)

def originalEndpoints (h : ReturnRows) : Endpoint :=
  ((h.1 0, h.2 0), (h.1 1, h.2 1))

/-- All original tuples in the long unit-middle chart with nonunit right side
have the required prime-cube error bound. Both parameter and endpoint counts
are derived from the original integer rows and the actual return word. -/
theorem actual_long_nonunit_rhs_tuple_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime) (X Y H : ℝ),
      0 < X → 0 < Y → 0 < H → H^2 = X*Y →
      (p : ℝ)^3 ≤ X*Y → X*Y ≤ (p : ℝ)^4 →
      2*X < (p^2 : ℕ) → 2*Y < (p^3 : ℕ) →
      ∀ (a₁ a₂ : ZMod (p^3)), IsUnit a₁ → IsUnit a₂ →
      ∀ T : Finset ReturnRows,
      (∀ h ∈ T, ∀ i, |(h.1 i : ℝ)| ≤ X ∧ |(h.2 i : ℝ)| ≤ Y) →
      (∀ h ∈ T, sixReturnWord a₁ a₂ (h.1 0) (h.2 2) (h.1 1)
        (h.2 0) (h.1 2) (h.2 1) = scalarReturn (-1)) →
      (∀ h ∈ T, IsUnit (h.1 2 : ZMod (p^3)) ∧ IsUnit (h.2 2 : ZMod (p^3))) →
      (∀ h ∈ T, (ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p))
        (1+a₁*a₂*(h.2 2 : ZMod (p^3))*(h.1 2 : ZMod (p^3))) = 0) →
      (∀ h ∈ T, ∃ B : ReducedMiddleBasis (p^3) (h.2 2) (h.1 2) X Y,
        (p : ℝ)^3 ≤ H*Real.sqrt (weightedSq X Y B.R)) →
      (T.card : ℝ) ≤ C*(p : ℝ)^ε*(X*Y)^2/(p : ℝ)^4 := by
  obtain ⟨C, hC, hparams⟩ := actual_nonunit_rhs_parameter_count ε hε
  refine ⟨194*C, by positivity, ?_⟩
  intro p hp X Y H hX hY hH hHsq harea hupper hXsmall hYsmall
    a₁ a₂ ha₁ ha₂ T hbox hword hunit hnonunit hlong
  classical
  letI : NeZero (p^3) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let ρ : ZMod (p^3) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (by decide : 3 ≠ 0)) (ZMod p)
  let params := T.image originalMiddle
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hparamcount : (params.card : ℝ) ≤ C*(p : ℝ)^ε*(1+X*Y/p) := by
    apply hparams p hp X Y hX hY hupper (ρ (a₁*a₂)) ((ha₁.mul ha₂).map ρ) params
    · intro wt hwt
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hwt
      exact hbox h hh 2
    · intro wt hwt
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hwt
      simpa only [originalMiddle, map_add, map_one, map_mul, map_intCast, mul_assoc,
        mul_left_comm, mul_comm] using hnonunit h hh
  have hfiber (wt : Coordinate) (hwt : wt ∈ params) :
      ((T.filter (fun h => originalMiddle h = wt)).card : ℝ) ≤
        97*(X*Y)/(p : ℝ)^3 := by
    obtain ⟨h₀, hh₀, he₀⟩ := Finset.mem_image.mp hwt
    obtain ⟨B, hB⟩ := hlong h₀ hh₀
    let S := T.filter fun h => originalMiddle h = wt
    let E := S.image originalEndpoints
    let F := (E.image Prod.fst) ∪ (E.image Prod.snd)
    have hwt₀ : wt.1 = h₀.1 2 ∧ wt.2 = h₀.2 2 := by
      exact ⟨(congrArg Prod.fst he₀).symm, (congrArg Prod.snd he₀).symm⟩
    have hS (h : ReturnRows) (hh : h ∈ S) :
        h ∈ T ∧ h.1 2 = h₀.1 2 ∧ h.2 2 = h₀.2 2 := by
      have hs := Finset.mem_filter.mp hh
      have hm : h.1 2 = wt.1 ∧ h.2 2 = wt.2 := by
        exact ⟨congrArg Prod.fst hs.2, congrArg Prod.snd hs.2⟩
      exact ⟨hs.1, hm.1.trans hwt₀.1, hm.2.trans hwt₀.2⟩
    have hE (e : Endpoint) (he : e ∈ E) :
        e.1 ∈ middleLattice (p^3) (h₀.2 2) (h₀.1 2) ∧
        e.2 ∈ middleLattice (p^3) (h₀.2 2) (h₀.1 2) ∧
        e.1 ∈ literalBox X Y ∧ e.2 ∈ literalBox X Y ∧
        sixReturnWord a₁ a₂ e.1.1 (h₀.2 2) e.2.1 e.1.2 (h₀.1 2) e.2.2 =
          scalarReturn (-1) := by
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hT, hwm, htm⟩ := hS h hh
      have heq := (sixReturnWord_minus_iff _ _ _ _ _ _ _ _ ha₁ ha₂).mp (hword h hT)
      have hm₁ : ((p^3 : ℕ) : ℤ) ∣ h.1 2*h.2 0-h.2 2*h.1 0 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        simpa only [Int.cast_sub, Int.cast_mul] using sub_eq_zero.mpr heq.2.2.1
      have hm₂ : ((p^3 : ℕ) : ℤ) ∣ h.1 2*h.2 1-h.2 2*h.1 1 := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        simpa only [Int.cast_sub, Int.cast_mul] using sub_eq_zero.mpr heq.2.2.2
      refine ⟨?_, ?_, hbox h hT 0, hbox h hT 1, ?_⟩
      · simpa only [originalEndpoints, middleLattice, Set.mem_setOf_eq,
          Prod.fst, Prod.snd, hwm, htm] using hm₁
      · simpa only [originalEndpoints, middleLattice, Set.mem_setOf_eq,
          Prod.fst, Prod.snd, hwm, htm] using hm₂
      · simpa only [originalEndpoints, hwm, htm] using hword h hT
    have hF (z : Coordinate) (hz : z ∈ F) :
        z ∈ middleLattice (p^3) (h₀.2 2) (h₀.1 2) ∧ z ∈ literalBox X Y := by
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨(hE e he).1, (hE e he).2.2.1⟩
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨(hE e he).2.1, (hE e he).2.2.2.1⟩
    have hinj : Set.InjOn originalEndpoints (S : Set ReturnRows) := by
      intro h hh h' hh' he
      have hb := hS h hh
      have hb' := hS h' hh'
      apply Prod.ext <;> funext i <;> fin_cases i
      · exact congrArg (fun e : Endpoint => e.1.1) he
      · exact congrArg (fun e : Endpoint => e.2.1) he
      · exact hb.2.1.trans hb'.2.1.symm
      · exact congrArg (fun e : Endpoint => e.1.2) he
      · exact congrArg (fun e : Endpoint => e.2.2) he
      · exact hb.2.2.trans hb'.2.2.symm
    have hsub : E ⊆ (F.product F).filter fun e => sixReturnWord a₁ a₂
        (e.1.1 : ZMod (p^3)) (h₀.2 2) e.2.1 e.1.2 (h₀.1 2) e.2.2 =
          scalarReturn (-1) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩),
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)⟩,
        (hE e he).2.2.2.2⟩
    calc
      (S.card : ℝ) = (E.card : ℝ) := by
        simp only [E, Finset.card_image_of_injOn hinj]
      _ ≤ (((F.product F).filter fun e => sixReturnWord a₁ a₂
          (e.1.1 : ZMod (p^3)) (h₀.2 2) e.2.1 e.1.2 (h₀.1 2) e.2.2 =
            scalarReturn (-1)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ 97*(X*Y)/(p : ℝ)^3 := long_actual_endpoint_pair_count hp hX hY hH hHsq
        harea hXsmall hYsmall a₁ a₂ ha₁ ha₂ (hunit h₀ hh₀).2 (hunit h₀ hh₀).1 B hB F
          (fun z hz => (hF z hz).1) (fun z hz => (hF z hz).2)
  have hcount : (T.card : ℝ) =
      ∑ wt ∈ params, ((T.filter (fun h => originalMiddle h = wt)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image originalMiddle T
  have hfactor : 0 ≤ 97*(X*Y)/(p : ℝ)^3 := by positivity
  have hA : 1 ≤ (X*Y)/(p : ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    nlinarith [sq_nonneg ((p : ℝ)-1)]
  calc
    (T.card : ℝ) = ∑ wt ∈ params, ((T.filter (fun h => originalMiddle h = wt)).card : ℝ) := hcount
    _ ≤ ∑ _wt ∈ params, 97*(X*Y)/(p : ℝ)^3 := Finset.sum_le_sum hfiber
    _ = (params.card : ℝ)*(97*(X*Y)/(p : ℝ)^3) := by simp
    _ ≤ (C*(p : ℝ)^ε*(1+X*Y/p))*(97*(X*Y)/(p : ℝ)^3) :=
      mul_le_mul_of_nonneg_right hparamcount hfactor
    _ ≤ (C*(p : ℝ)^ε*(2*(X*Y/p)))*(97*(X*Y)/(p : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_right _ hfactor
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (194*C)*(p : ℝ)^ε*(X*Y)^2/(p : ℝ)^4 := by field_simp; ring

end

end D5.S3.Arith.CharacterSums.Original
