/- GID: D5/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUB/BCCBOrderNineAffineSuborbits
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Affine order nine BCCB suborbits have a cancelling pair or an equilateral triple. -/

import D5.S3.Observer.WindowRegister

/-! Affine dephasings of the BCCB family with four unit parameters summing to one
are contained in the cancelling-pair or equilateral-triple families. -/

noncomputable section

open scoped BigOperators Topology ComplexConjugate
open Complex

namespace D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits

local notation "omega" => D5.S3.Observer.WindowRegister.windowRoot 3

def bccb (x y u w : ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  !![1,x,x,y,u,w,y,w,u;
     x,1,x,w,y,u,u,y,w;
     x,x,1,u,w,y,w,u,y;
     y,w,u,1,x,x,y,u,w;
     u,y,w,x,1,x,w,y,u;
     w,u,y,x,x,1,u,w,y;
     y,u,w,y,w,u,1,x,x;
     w,y,u,u,y,w,x,1,x;
     u,w,y,w,u,y,x,x,1]

def dephase (H : Matrix (Fin 9) (Fin 9) ℂ) : Matrix (Fin 9) (Fin 9) ℂ :=
  fun a b => H a b / (H a 0 * H 0 b)

def params {p : ℕ} (x y u w : (Fin p → ℝ) → ℂ) (t : Fin p → ℝ) : Fin 4 → ℂ :=
  ![x t, y t, u t, w t]

def IsAffineOn {p : ℕ} (U : Set (Fin p → ℝ))
    (F : (Fin p → ℝ) → Matrix (Fin 9) (Fin 9) ℂ) : Prop :=
  ∀ a b, ∃ (c : ℂ) (L : (Fin p → ℝ) →ₗ[ℝ] ℝ),
    ∀ t ∈ U, F t a b = c * Complex.exp ((L t : ℂ) * I)

def claim : Prop :=
  ∀ (p : ℕ) (U : Set (Fin p → ℝ)), IsOpen U → U.Nonempty →
    ∀ x y u w : (Fin p → ℝ) → ℂ,
      (∀ t ∈ U, ‖x t‖ = 1 ∧ ‖y t‖ = 1 ∧ ‖u t‖ = 1 ∧ ‖w t‖ = 1 ∧
        x t + y t + u t + w t = 1) →
      IsAffineOn U (fun t => dephase (bccb (x t) (y t) (u t) (w t))) →
      (∃ t₁ ∈ U, ∃ t₂ ∈ U, params x y u w t₁ ≠ params x y u w t₂) →
      ∃ π : Equiv.Perm (Fin 4),
        (∃ μ : (Fin p → ℝ) → ℂ, ∀ t ∈ U,
          params x y u w t ∘ π = ![μ t, -μ t, -omega, -omega ^ 2]) ∨
        (∃ ξ : (Fin p → ℝ) → ℂ, ∀ t ∈ U,
          params x y u w t ∘ π = ![1, ξ t, omega * ξ t, omega ^ 2 * ξ t])

private def phaseCharacter {p : ℕ} (L : (Fin p → ℝ) →ₗ[ℝ] ℝ) :
    Multiplicative (Fin p → ℝ) →* ℂ :=
  Circle.coeHom.comp ((Real.probChar.compAddMonoidHom L.toAddMonoidHom).toMonoidHom)

private lemma phase_analytic {p : ℕ} (L : (Fin p → ℝ) →ₗ[ℝ] ℝ) (t : Fin p → ℝ) :
    AnalyticAt ℝ (fun s => Complex.exp ((L s : ℂ) * I)) t := by
  have h : AnalyticAt ℝ (fun s => (L s : ℂ) * I) t :=
    ((Complex.ofRealCLM.analyticAt (L t)).comp (L.toContinuousLinearMap.analyticAt t)).mul
      analyticAt_const
  exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp h

open scoped Classical in
private lemma character_coefficients {p n : ℕ} {U : Set (Fin p → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) (c : Fin n → ℂ)
    (L : Fin n → (Fin p → ℝ) →ₗ[ℝ] ℝ)
    (hs : ∀ t ∈ U, ∑ j, c j * Complex.exp ((L j t : ℂ) * I) = 1)
    (χ : Multiplicative (Fin p → ℝ) →* ℂ) :
    (∑ j, if phaseCharacter (L j) = χ then c j else 0) = if χ = 1 then 1 else 0 := by
  classical
  have ha : AnalyticOnNhd ℝ (fun t => ∑ j, c j * Complex.exp ((L j t : ℂ) * I))
      Set.univ := by
    intro t _
    exact Finset.analyticAt_fun_sum _ (fun j _ => analyticAt_const.mul (phase_analytic (L j) t))
  obtain ⟨t₀, ht₀⟩ := hne
  have hg : (fun t => ∑ j, c j * Complex.exp ((L j t : ℂ) * I)) = fun _ => 1 :=
    ha.eq_of_eventuallyEq analyticOnNhd_const
      (Filter.eventually_of_mem (hU.mem_nhds ht₀) (fun t ht => hs t ht))
  have he : (∑ j, Finsupp.single (phaseCharacter (L j)) (c j)) =
      Finsupp.single (1 : Multiplicative (Fin p → ℝ) →* ℂ) (1 : ℂ) := by
    have hlin := linearIndependent_monoidHom (Multiplicative (Fin p → ℝ)) ℂ
    apply hlin.finsuppLinearCombination_injective
    simp only [map_sum, Finsupp.linearCombination_single]
    ext t
    have hphase (j) : phaseCharacter (L j) t =
        Complex.exp ((L j (Multiplicative.toAdd t) : ℂ) * I) := by
      change (Real.probChar (L j (Multiplicative.toAdd t)) : ℂ) = _
      exact Real.probChar_apply _
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hphase,
      MonoidHom.one_apply, one_mul] using
      congrFun hg (Multiplicative.toAdd t)
  have hh := congrArg (fun f => f χ) he
  simpa only [Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm] using hh

private lemma inverse_affine {p : ℕ} {U : Set (Fin p → ℝ)} (hne : U.Nonempty)
    (f : (Fin p → ℝ) → ℂ) (hf : ∀ t ∈ U, ‖f t‖ = 1)
    (c : ℂ) (L : (Fin p → ℝ) →ₗ[ℝ] ℝ)
    (he : ∀ t ∈ U, (f t)⁻¹ = c * Complex.exp ((L t : ℂ) * I)) :
    ∃ (d : ℂ) (M : (Fin p → ℝ) →ₗ[ℝ] ℝ), ‖d‖ = 1 ∧
      ∀ t ∈ U, f t = d * Complex.exp ((M t : ℂ) * I) := by
  refine ⟨c⁻¹, -L, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hne
    have hn := congrArg norm (he t ht)
    rw [norm_inv, hf t ht, inv_one, norm_mul, norm_exp_ofReal_mul_I, mul_one] at hn
    simp [norm_inv, ← hn]
  · intro t ht
    have hh := congrArg Inv.inv (he t ht)
    simpa [mul_inv, ← Complex.exp_neg, mul_comm] using hh

private lemma affine_parameters {p : ℕ} {U : Set (Fin p → ℝ)} (hne : U.Nonempty)
    (x y u w : (Fin p → ℝ) → ℂ)
    (hn : ∀ t ∈ U, ‖x t‖ = 1 ∧ ‖y t‖ = 1 ∧ ‖u t‖ = 1 ∧ ‖w t‖ = 1)
    (ha : IsAffineOn U (fun t => dephase (bccb (x t) (y t) (u t) (w t)))) :
    ∃ (c : Fin 4 → ℂ) (L : Fin 4 → (Fin p → ℝ) →ₗ[ℝ] ℝ),
      (∀ j, ‖c j‖ = 1) ∧
      ∀ t ∈ U, ∀ j, params x y u w t j = c j * Complex.exp ((L j t : ℂ) * I) := by
  obtain ⟨a, A, hA⟩ := ha 1 2
  obtain ⟨b, B, hB⟩ := ha 3 6
  obtain ⟨d, D, hD⟩ := ha 4 8
  obtain ⟨e, E, hE⟩ := ha 5 7
  have hA' : ∀ t ∈ U, (x t)⁻¹ = a * Complex.exp ((A t : ℂ) * I) := by
    intro t ht
    simpa [dephase, bccb, div_self_mul_self'] using hA t ht
  have hB' : ∀ t ∈ U, (y t)⁻¹ = b * Complex.exp ((B t : ℂ) * I) := by
    intro t ht
    simpa [dephase, bccb, div_self_mul_self'] using hB t ht
  have hD' : ∀ t ∈ U, (u t)⁻¹ = d * Complex.exp ((D t : ℂ) * I) := by
    intro t ht
    simpa [dephase, bccb, div_self_mul_self'] using hD t ht
  have hE' : ∀ t ∈ U, (w t)⁻¹ = e * Complex.exp ((E t : ℂ) * I) := by
    intro t ht
    simpa [dephase, bccb, div_self_mul_self'] using hE t ht
  obtain ⟨a', A', na, ea⟩ := inverse_affine hne x (fun t ht => (hn t ht).1) a A hA'
  obtain ⟨b', B', nb, eb⟩ := inverse_affine hne y (fun t ht => (hn t ht).2.1) b B hB'
  obtain ⟨d', D', nd, ed⟩ := inverse_affine hne u (fun t ht => (hn t ht).2.2.1) d D hD'
  obtain ⟨e', E', ne, ee⟩ := inverse_affine hne w (fun t ht => (hn t ht).2.2.2) e E hE'
  refine ⟨![a', b', d', e'], ![A', B', D', E'], ?_, ?_⟩
  · intro j; fin_cases j <;> simp [na, nb, nd, ne]
  · intro t ht j; fin_cases j <;> simp [params, ea t ht, eb t ht, ed t ht, ee t ht]

private lemma four_permutation (a b c d : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ π : Equiv.Perm (Fin 4), (π : Fin 4 → Fin 4) = ![a, b, c, d] := by
  have hinj : Function.Injective (![a, b, c, d] : Fin 4 → Fin 4) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), rfl⟩

open scoped Classical in
private lemma four_character_classes {M : Type*} [One M] (f : Fin 4 → M)
    (c : Fin 4 → ℂ) (hc : ∀ j, c j ≠ 0)
    (hs : ∀ q, (∑ j, if f j = q then c j else 0) = if q = 1 then 1 else 0)
    (hn : ∃ j, f j ≠ 1) :
    ∃ (π : Equiv.Perm (Fin 4)) (q : M), q ≠ 1 ∧
      (f ∘ π = ![q, q, 1, 1] ∨ f ∘ π = ![1, q, q, q]) := by
  classical
  let fiber (q : M) := Finset.univ.filter (fun j => f j = q)
  have hmem (q : M) (j : Fin 4) : j ∈ fiber q ↔ f j = q := by simp [fiber]
  have hsum (q : M) : ∑ j ∈ fiber q, c j = if q = 1 then 1 else 0 := by
    simpa [fiber, Finset.sum_filter] using hs q
  have hz : (fiber 1).Nonempty := by
    by_contra hh
    have he : fiber 1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hh
    simpa [he] using hsum 1
  obtain ⟨z, hz⟩ := hz
  have hz' : f z = 1 := (hmem 1 z).mp hz
  have hlarge (q : M) (hq : q ≠ 1) (hne : (fiber q).Nonempty) :
      2 ≤ (fiber q).card := by
    have hp := Finset.card_pos.mpr hne
    by_contra hh
    have hcard : (fiber q).card = 1 := by omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have he := hsum q
    rw [hj] at he
    exact hc j (by simpa [hq] using he)
  obtain ⟨j, hj⟩ := hn
  let q := f j
  have hq : q ≠ 1 := hj
  have hS : (fiber q).Nonempty := ⟨j, (hmem q j).mpr rfl⟩
  have hlow := hlarge q hq hS
  have hznot : z ∉ fiber q := by
    intro hh
    exact hq ((hmem q z).mp hh ▸ hz')
  have hbound : (fiber q).card ≤ 3 := by
    have hh : (insert z (fiber q)).card ≤ 4 := by
      simpa using (Finset.card_le_univ (insert z (fiber q)))
    rw [Finset.card_insert_of_notMem hznot] at hh
    omega
  have hrest (k : Fin 4) (hk : k ∉ fiber q) : f k = 1 := by
    by_contra hk1
    have hkq : f k ≠ q := by simpa [hmem] using hk
    have hT := hlarge (f k) hk1 ⟨k, (hmem (f k) k).mpr rfl⟩
    have hd : Disjoint (fiber q) (fiber (f k)) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hkq (((hmem (f k) a).mp hb).symm.trans ((hmem q a).mp ha))
    have hzz : z ∉ fiber q ∪ fiber (f k) := by
      simp only [Finset.mem_union, not_or]
      refine ⟨hznot, ?_⟩
      intro hh
      exact hk1 (((hmem (f k) z).mp hh).symm.trans hz')
    have hh : (insert z (fiber q ∪ fiber (f k))).card ≤ 4 := by
      simpa using (Finset.card_le_univ (insert z (fiber q ∪ fiber (f k))))
    rw [Finset.card_insert_of_notMem hzz, Finset.card_union_of_disjoint hd] at hh
    omega
  let T := Finset.univ \ fiber q
  have hTmem (k : Fin 4) : k ∈ T ↔ k ∉ fiber q := by simp [T]
  have hTcard : T.card = 4 - (fiber q).card := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hsplit : (fiber q).card = 2 ∨ (fiber q).card = 3 := by omega
  rcases hsplit with htwo | hthree
  · obtain ⟨a, b, hab, habS⟩ := Finset.card_eq_two.mp htwo
    obtain ⟨d, e, hde, hdeT⟩ := Finset.card_eq_two.mp (show T.card = 2 by omega)
    have ha : a ∈ fiber q := by simp [habS]
    have hb : b ∈ fiber q := by simp [habS]
    have hd : d ∉ fiber q := (hTmem d).mp (by simp [hdeT])
    have he : e ∉ fiber q := (hTmem e).mp (by simp [hdeT])
    obtain ⟨π, hπ⟩ := four_permutation a b d e hab
      (fun h => hd (h ▸ ha)) (fun h => he (h ▸ ha))
      (fun h => hd (h ▸ hb)) (fun h => he (h ▸ hb)) hde
    refine ⟨π, q, hq, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hπ, (hmem q a).mp ha,
      (hmem q b).mp hb, hrest d hd, hrest e he]
  · obtain ⟨a, b, d, hab, had, hbd, habdS⟩ := Finset.card_eq_three.mp hthree
    obtain ⟨e, heT⟩ := Finset.card_eq_one.mp (show T.card = 1 by omega)
    have ha : a ∈ fiber q := by simp [habdS]
    have hb : b ∈ fiber q := by simp [habdS]
    have hd : d ∈ fiber q := by simp [habdS]
    have he : e ∉ fiber q := (hTmem e).mp (by simp [heT])
    obtain ⟨π, hπ⟩ := four_permutation e a b d
      (fun h => he (h.symm ▸ ha)) (fun h => he (h.symm ▸ hb))
      (fun h => he (h.symm ▸ hd)) hab had hbd
    refine ⟨π, q, hq, Or.inr ?_⟩
    funext k
    fin_cases k <;> simp [hπ, (hmem q a).mp ha,
      (hmem q b).mp hb, (hmem q d).mp hd, hrest e he]

private lemma unit_pair (b c : ℂ) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : b + c = 1) :
    (b = -omega ∧ c = -omega ^ 2) ∨ (b = -omega ^ 2 ∧ c = -omega) := by
  have hp : IsPrimitiveRoot omega 3 :=
    D5.S3.Observer.WindowRegister.windowRoot_isPrimitiveRoot 3
  have hroot : 1 + omega + omega ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hp.geom_sum_eq_zero (by norm_num : 1 < 3)
  have hd : ‖b - 1‖ = 1 := by
    rw [show b - 1 = -c by linear_combination hs, norm_neg, hc]
  have hr := Complex.norm_sub_one_sq_eq_of_norm_eq_one hb
  rw [hd] at hr
  have hbconj : b + conj b = 1 := by
    apply Complex.ext <;> simp
    linarith
  have hn : b * conj b = 1 := by rw [Complex.mul_conj', hb]; norm_num
  have hpoly : b ^ 2 - b + 1 = 0 := by linear_combination b * hbconj - hn
  have hfac : (b + omega) * (b + omega ^ 2) = 0 := by
    linear_combination hpoly + b * hroot + hp.pow_eq_one
  rcases mul_eq_zero.mp hfac with h | h
  · left
    constructor
    · linear_combination h
    · linear_combination hs - h + hroot
  · right
    constructor
    · linear_combination h
    · linear_combination hs - h + hroot

private lemma unit_triple (a b c : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hs : a + b + c = 0) :
    (b = omega * a ∧ c = omega ^ 2 * a) ∨
      (b = omega ^ 2 * a ∧ c = omega * a) := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hs' : -b / a + -c / a = 1 := by field_simp; linear_combination -hs
  have hb' : ‖-b / a‖ = 1 := by rw [norm_div, norm_neg, hb, ha, div_one]
  have hc' : ‖-c / a‖ = 1 := by rw [norm_div, norm_neg, hc, ha, div_one]
  rcases unit_pair (-b / a) (-c / a) hb' hc' hs' with ⟨h, k⟩ | ⟨h, k⟩
  · left
    constructor
    · field_simp at h; linear_combination -h
    · field_simp at k; linear_combination -k
  · right
    constructor
    · field_simp at h; linear_combination -h
    · field_simp at k; linear_combination -k

theorem result : claim := by
  classical
  intro p U hU hne x y u w hn ha hnon
  obtain ⟨c, L, hc, he⟩ := affine_parameters hne x y u w
    (fun t ht => ⟨(hn t ht).1, (hn t ht).2.1, (hn t ht).2.2.1,
      (hn t ht).2.2.2.1⟩) ha
  let f : Fin 4 → Multiplicative (Fin p → ℝ) →* ℂ := fun j => phaseCharacter (L j)
  have hrep (t) (ht : t ∈ U) (j) :
      params x y u w t j = c j * f j (Multiplicative.ofAdd t) := he t ht j
  have hs : ∀ q, (∑ j, if f j = q then c j else 0) = if q = 1 then 1 else 0 := by
    intro q
    apply character_coefficients hU hne c L _ q
    intro t ht
    rw [show (∑ j, c j * Complex.exp ((L j t : ℂ) * I)) =
      ∑ j, params x y u w t j from Finset.sum_congr rfl (fun j _ => (he t ht j).symm)]
    simpa [params, Fin.sum_univ_succ, add_assoc] using (hn t ht).2.2.2.2
  have hcn (j) : c j ≠ 0 := norm_ne_zero_iff.mp (by rw [hc j]; norm_num)
  have hfn : ∃ j, f j ≠ 1 := by
    by_contra hh
    push Not at hh
    obtain ⟨t, ht, s, hs, hts⟩ := hnon
    apply hts
    funext j
    rw [hrep t ht j, hrep s hs j, hh j]
    rfl
  obtain ⟨π, q, hq, hpair | htriple⟩ := four_character_classes f c hcn hs hfn
  · have hf (j) : f (π j) = (![q, q, 1, 1] : Fin 4 → _) j := congrFun hpair j
    have hzero : c (π 0) + c (π 1) = 0 := by
      have hh := hs q
      rw [← Equiv.sum_comp π (fun j => if f j = q then c j else 0)] at hh
      simpa [Fin.sum_univ_succ, hf, hq, Ne.symm hq] using hh
    have hone : c (π 2) + c (π 3) = 1 := by
      have hh := hs 1
      rw [← Equiv.sum_comp π (fun j => if f j = 1 then c j else 0)] at hh
      simpa [Fin.sum_univ_succ, hf, hq] using hh
    have hc1 : c (π 1) = -c (π 0) := by linear_combination hzero
    let μ := fun t => c (π 0) * q (Multiplicative.ofAdd t)
    have htable (t) (ht : t ∈ U) :
        params x y u w t ∘ π = ![μ t, -μ t, c (π 2), c (π 3)] := by
      funext j
      fin_cases j <;> simp [hrep t ht, hf, hc1, μ]
    rcases unit_pair (c (π 2)) (c (π 3)) (hc _) (hc _) hone with ⟨hb, hd⟩ | ⟨hb, hd⟩
    · refine ⟨π, Or.inl ⟨μ, ?_⟩⟩
      intro t ht
      simpa [hb, hd] using htable t ht
    · refine ⟨(Equiv.swap 2 3).trans π, Or.inl ⟨μ, ?_⟩⟩
      intro t ht
      funext j
      have hh := congrFun (htable t ht) ((Equiv.swap (2 : Fin 4) 3) j)
      fin_cases j <;> simpa [Function.comp_def, Equiv.swap_apply_def, hb, hd] using hh
  · have hf (j) : f (π j) = (![1, q, q, q] : Fin 4 → _) j := congrFun htriple j
    have hone : c (π 0) = 1 := by
      have hh := hs 1
      rw [← Equiv.sum_comp π (fun j => if f j = 1 then c j else 0)] at hh
      simpa [Fin.sum_univ_succ, hf, hq] using hh
    have hzero : c (π 1) + c (π 2) + c (π 3) = 0 := by
      have hh := hs q
      rw [← Equiv.sum_comp π (fun j => if f j = q then c j else 0)] at hh
      simpa [Fin.sum_univ_succ, hf, hq, Ne.symm hq, add_assoc] using hh
    let ξ := fun t => c (π 1) * q (Multiplicative.ofAdd t)
    rcases unit_triple (c (π 1)) (c (π 2)) (c (π 3)) (hc _) (hc _) (hc _) hzero with
      ⟨hb, hd⟩ | ⟨hb, hd⟩
    · refine ⟨π, Or.inr ⟨ξ, ?_⟩⟩
      intro t ht
      funext j
      fin_cases j <;> simp [hrep t ht, hf, hone, hb, hd, ξ, mul_assoc]
    · refine ⟨(Equiv.swap 2 3).trans π, Or.inr ⟨ξ, ?_⟩⟩
      intro t ht
      funext j
      fin_cases j <;>
        simp [Function.comp_def, Equiv.swap_apply_def, hrep t ht, hf, hone, hb, hd, ξ, mul_assoc]

end D5.S3.Quantum.Tomography.MUB.BCCBOrderNineAffineSuborbits
