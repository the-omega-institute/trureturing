/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact common-group growth profiles for all odd square displacements. -/

import D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth

/-! The existing primitive-coordinate supplier is reused for both actual quotients.
The new content is the all-q three-regime gap and its unique discrete peak. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth

open BajnokBeattySameGroupGrowth BajnokBeattyAsymmetricGrowth BajnokBeattyExtremalGrowth
open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity
open scoped Classical

/-!
The square-displacement extension keeps the same actual quotient construction.
Its live new content is the q-dependent primitive row and discrete comparison
of the two actual cap differences. In particular the two boundary values are
separated by (q-1)*(q-3)*p/2+1, which is positive even when q=3.
The hypothesis q+1 ≤ 2*t is equivalent to (q+1)/2 ≤ t for odd q.
-/

/-- For all odd integers p,q ≥ 3 and q+1 ≤ 2*t, the actual quotients with
displacements (1,q^2) and (q,q) have the same noncyclic underlying group,
the same exact diameter, and the stated complete actual ball-gap profile.
All divisions in the statement are integer divisions. In particular the
unique peak formula specializes at q=3 to 2*p^2-2*p+1. -/
theorem same_group_square_displacement_growth (p q t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (hq3 : 3 ≤ q) (hqo : Odd q)
    (ht : q+1 ≤ 2*t) :
    let m : ℤ := 2*q*t-1
    let D : ℤ := (m^2-q^2)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v11 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v21 : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
    let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
    let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
    let K1 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v11, v21])
    let Kq : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1q, v2q])
    let G1 := Plane ⧸ K1
    let Gq := Plane ⧸ Kq
    let F1 : Plane →+ G1 := K1.mkQ.toAddMonoidHom
    let Fq : Plane →+ Gq := Kq.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f1 : (ℤ × ℤ) →+ G1 := F1.comp E.symm.toLinearMap.toAddMonoidHom
    let fq : (ℤ × ℤ) →+ Gq := Fq.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c1 : ℕ → ℕ := fun r => ((leeDiamond r).image f1).card
    let cq : ℕ → ℕ := fun r => ((leeDiamond r).image fq).card
    let gap : ℕ → ℤ := fun r => (c1 r : ℤ)-(cq r : ℤ)
    let M : ℤ := (q-1)^2*p^2/2-(q-1)*p+1
    ∃ (e1 : G1 ≃+ H) (eq : Gq ≃+ H),
      (∀ z : Plane, e1 (F1 z) =
        (((-z 0+z 1 : ℤ) : ZMod p.natAbs),
          ((-(q*t)*z 0+(q*t-1)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ z : Plane, eq (Fq z) =
        ((((-2*t-1)*z 0+(2*t-1)*z 1 : ℤ) : ZMod p.natAbs),
          ((-(q*t+(q-1)/2)*z 0+(q*t-(q+1)/2)*z 1 : ℤ) :
            ZMod (p*D).natAbs))) ∧
      ¬ IsAddCyclic H ∧
      (∀ R : ℕ, LeeCovers F1 (R : ℤ) ↔ s ≤ R) ∧
      (∀ R : ℕ, LeeCovers Fq (R : ℤ) ↔ s ≤ R) ∧
      (∀ r : ℕ, cq r ≤ c1 r ∧
        (cq r < c1 r ↔ p*(m-q)/2 ≤ (r : ℤ) ∧ r < s)) ∧
      (∀ r : ℕ, r ≤ s →
        let δ : ℤ := p*m-(2*(r : ℤ)+1)
        0 ≤ δ ∧ Even δ ∧
          (q*p ≤ δ → gap r = 0) ∧
          (p ≤ δ → δ < q*p → 2*gap r = (q*p-δ)^2+1) ∧
          (δ < p → 2*gap r = (q-1)^2*p*δ)) ∧
      (∀ r : ℕ, s ≤ r →
        (c1 r : ℤ) = p^2*D ∧ (cq r : ℤ) = p^2*D) ∧
      (∀ r : ℕ, gap r ≤ M) ∧
      (∀ r : ℕ, gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) ∧
      (0 ≤ p*(m-1)/2-1) ∧
      (∃! r : ℕ, gap r = M) ∧
      gap (s-1) = (q-1)^2*p ∧
      ¬ ∃ e : G1 ≃+ Gq,
        e (F1 ![1, 0]) = Fq ![1, 0] ∧
        e (F1 ![0, 1]) = Fq ![0, 1] := by
  classical
  let m : ℤ := 2*q*t-1
  let D : ℤ := (m^2-q^2)/2
  let H := ZMod p.natAbs × ZMod (p*D).natAbs
  let v11 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v21 : Plane := ![p*(m-q^2)/2, -(p*(m+q^2)/2)]
  let v1q : Plane := ![p*(m-q)/2, p*(m+q)/2]
  let v2q : Plane := ![p*(m-q)/2, -(p*(m+q)/2)]
  let K1 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v11, v21])
  let Kq : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1q, v2q])
  let G1 := Plane ⧸ K1
  let Gq := Plane ⧸ Kq
  let F1 : Plane →+ G1 := K1.mkQ.toAddMonoidHom
  let Fq : Plane →+ Gq := Kq.mkQ.toAddMonoidHom
  let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
  let f1 : (ℤ × ℤ) →+ G1 := F1.comp E.symm.toLinearMap.toAddMonoidHom
  let fq : (ℤ × ℤ) →+ Gq := Fq.comp E.symm.toLinearMap.toAddMonoidHom
  let s : ℕ := ((p*m-1)/2).toNat
  let c1 : ℕ → ℕ := fun r => ((leeDiamond r).image f1).card
  let cq : ℕ → ℕ := fun r => ((leeDiamond r).image fq).card
  let gap : ℕ → ℤ := fun r => (c1 r : ℤ)-(cq r : ℤ)
  let M : ℤ := (q-1)^2*p^2/2-(q-1)*p+1
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  have hqSquare : 9 ≤ q^2 := by nlinarith only [hq3, sq_nonneg (q-3)]
  have hqSquareLt : q^2 < m := by
    have hprod := mul_nonneg (le_of_lt hq) (show 0 ≤ 2*t-q-1 by omega)
    dsimp only [m]
    nlinarith only [hprod, hq3]
  have hm11 : 11 ≤ m := by
    have ht2 : 2 ≤ t := by omega
    have hprod := mul_nonneg (show 0 ≤ q-3 by omega) (show 0 ≤ t-2 by omega)
    dsimp only [m]
    nlinarith only [hprod, hq3, ht2]
  have hqm : q < m := by nlinarith only [hqSquareLt, hq3, sq_nonneg (q-1)]
  have hmo : Odd m := ⟨q*t-1, by dsimp only [m]; ring⟩
  have hq2o : Odd (q^2) := by simpa only [pow_two] using hqo.mul hqo
  have half_exact (c d : ℤ) (h : c = 2*d) : c/2 = d := by omega
  have twice_half (c : ℤ) (hc : Even c) : 2*(c/2) = c := by
    simpa only [mul_comm] using Int.ediv_mul_cancel hc.two_dvd
  have hqm2 : 2*((q-1)/2) = q-1 := twice_half _ (hqo.sub_odd odd_one)
  have hqp2 : 2*((q+1)/2) = q+1 := twice_half _ (hqo.add_odd odd_one)
  have hD2 : 2*D = m^2-q^2 := by
    apply twice_half
    simpa only [pow_two] using (hmo.mul hmo).sub_odd (hqo.mul hqo)
  have hDpos : 0 < D := by
    have hprod := mul_pos (sub_pos.mpr hqm) (show 0 < m+q by omega)
    nlinarith only [hD2, hprod]
  have hhalfCard : p^2*(m^2-q^2)/2 = p^2*D := by
    apply half_exact
    rw [← hD2]
    ring
  obtain ⟨hf1, hn1, hc1, hcount1, _hcov1, _hncov1, hdiam1⟩ :=
    asymmetric_quotient_growth p m 1 (q^2) hp3 hpo hmo
      odd_one hq2o (by norm_num) (by omega) (by positivity) hqSquareLt
  obtain ⟨hfq, _hnq, hcq, hcountq, _hcovq, _hncovq, hdiamq⟩ :=
    asymmetric_quotient_growth p m q q hp3 hpo hmo hqo hqo hq hqm hq hqm
  have hcard1 : (Nat.card G1 : ℤ) = p^2*D := by
    calc
      _ = p^2*(m^2-q^2)/2 := by simpa only [one_mul] using hc1
      _ = p^2*D := hhalfCard
  have hcardq : (Nat.card Gq : ℤ) = p^2*D := by
    calc
      _ = p^2*(m^2-q^2)/2 := by simpa only [pow_two] using hcq
      _ = p^2*D := hhalfCard

  -- Normalize all primitive halves before descending either quotient.
  let x : ℤ := q*t-(q+1)/2
  let y : ℤ := q*t+(q-1)/2
  let u : ℤ := (m-q^2)/2
  let v : ℤ := -((m+q^2)/2)
  have hx2 : 2*x = m-q := by dsimp only [x, m]; nlinarith only [hqp2]
  have hy2 : 2*y = m+q := by dsimp only [y, m]; nlinarith only [hqm2]
  have hu2 : 2*u = m-q^2 := twice_half _ (hmo.sub_odd hq2o)
  have hv2 : 2*v = -(m+q^2) := by
    have hh := twice_half _ (hmo.add_odd hq2o)
    dsimp only [v]
    omega
  have hx12 : 2*(q*t-1) = m-1 := by dsimp only [m]; ring
  have hy12 : 2*(q*t) = m+1 := by dsimp only [m]; ring
  have hv11 : v11 = ![p*(q*t-1), p*(q*t)] := by
    ext i
    fin_cases i
    · change p*(m-1)/2 = p*(q*t-1)
      apply half_exact
      rw [← hx12]
      ring
    · change p*(m+1)/2 = p*(q*t)
      apply half_exact
      rw [← hy12]
      ring
  have hv21 : v21 = ![p*u, p*v] := by
    ext i
    fin_cases i
    · change p*(m-q^2)/2 = p*u
      apply half_exact
      rw [← hu2]
      ring
    · change -(p*(m+q^2)/2) = p*v
      have hh : p*(m+q^2)/2 = -(p*v) := by
        apply half_exact
        rw [show m+q^2 = -(2*v) by omega]
        ring
      rw [hh]
      ring
  have hv1q : v1q = ![p*x, p*y] := by
    ext i
    fin_cases i
    · change p*(m-q)/2 = p*x
      apply half_exact
      rw [← hx2]
      ring
    · change p*(m+q)/2 = p*y
      apply half_exact
      rw [← hy2]
      ring
  have hv2q : v2q = ![p*x, p*(-y)] := by
    ext i
    fin_cases i
    · change p*(m-q)/2 = p*x
      apply half_exact
      rw [← hx2]
      ring
    · change -(p*(m+q)/2) = p*(-y)
      have hh : p*(m+q)/2 = p*y := by
        apply half_exact
        rw [← hy2]
        ring
      rw [hh]
      ring
  have hbezq : (-2*t-1)*x+(2*t-1)*y = 1 := by
    have hdouble : 2*((-2*t-1)*x+(2*t-1)*y) = 2 := by
      calc
        _ = (-2*t-1)*(2*x)+(2*t-1)*(2*y) := by ring
        _ = (-2*t-1)*(m-q)+(2*t-1)*(m+q) := by rw [hx2, hy2]
        _ = 2 := by dsimp only [m]; ring
    omega
  have hdet1 : (q*t-1)*v-(q*t)*u = -D := by
    have hfour : 4*((q*t-1)*v-(q*t)*u) = -2*(m^2-q^2) := by
      calc
        _ = (2*(q*t-1))*(2*v)-(2*(q*t))*(2*u) := by ring
        _ = (m-1)*(-(m+q^2))-(m+1)*(m-q^2) := by
          rw [hx12, hy12, hu2, hv2]
        _ = -2*(m^2-q^2) := by ring
    omega
  have hdetq : x*(-y)-y*x = -D := by
    have hfour : 4*(x*(-y)-y*x) = -2*(m^2-q^2) := by
      calc
        _ = -2*((2*x)*(2*y)) := by ring
        _ = -2*((m-q)*(m+q)) := by rw [hx2, hy2]
        _ = -2*(m^2-q^2) := by ring
    omega
  obtain ⟨e1, he1⟩ := same_group_coordinate_descent
    p D (q*t-1) (q*t) u v (-1) 1 v11 v21 hp hDpos
    (by ring) hdet1 hv11 hv21 hcard1
  obtain ⟨eq, heq⟩ := same_group_coordinate_descent
    p D x y x (-y) (-2*t-1) (2*t-1) v1q v2q hp hDpos
    hbezq hdetq hv1q hv2q hcardq
  have hnoncyclic : ¬ IsAddCyclic H := by
    intro hcyclic
    letI : IsAddCyclic H := hcyclic
    exact hn1 (isAddCyclic_of_surjective e1.symm.toAddMonoidHom e1.symm.surjective)
  letI : Finite G1 := hf1
  letI : Finite Gq := hfq
  letI : Fintype G1 := Fintype.ofFinite G1
  letI : Fintype Gq := Fintype.ofFinite Gq
  have hsZ : 2*((p*m-1)/2) = p*m-1 :=
    twice_half _ ((hpo.mul hmo).sub_odd odd_one)
  have hpm : 33 ≤ p*m := by
    have hprod := mul_nonneg (show 0 ≤ p-3 by omega) (show 0 ≤ m-11 by omega)
    nlinarith only [hp3, hm11, hprod]
  have hsCast : (s : ℤ) = (p*m-1)/2 := Int.toNat_of_nonneg (by omega)
  have hs : 2*(s : ℤ)+1 = p*m := by omega
  have hspos : 1 ≤ s := by omega
  have hsm : ((s-1 : ℕ) : ℤ) = (s : ℤ)-1 := by omega
  have hstart2 : 2*(p*(m-q)/2) = p*(m-q) :=
    twice_half _ ((hmo.sub_odd hqo).mul_left p)
  have hpeak2 : 2*(p*(m-1)/2-1) = p*(m-1)-2 := by
    have hh := twice_half _ ((hmo.sub_odd odd_one).mul_left p)
    omega
  have hpeakLt : p*(m-1)/2-1 < (s : ℤ) := by
    nlinarith only [hs, hpeak2, hp3]
  let A : ℤ := (q-1)*p
  let C : ℤ := (q-1)^2*p
  have hA : 2*p ≤ A := by
    dsimp only [A]
    exact mul_le_mul_of_nonneg_right (by omega) (le_of_lt hp)
  have hApos : 0 < A := by omega
  have hCpos : 0 < C := mul_pos (sq_pos_of_pos (by omega)) hp
  have hqp : q*p = A+p := by dsimp only [A]; ring
  have hq2p : p ≤ q^2*p := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ q^2 by omega) (le_of_lt hp)
  have hAeven : Even A := (hqo.sub_odd odd_one).mul_right p
  have hMsquare : (q-1)^2*p^2 = A^2 := by dsimp only [A]; ring
  have hM2 : 2*M = A^2-2*A+2 := by
    have hhalf := twice_half (A^2) (by simpa only [pow_two] using hAeven.mul_right A)
    dsimp only [M]
    rw [hMsquare]
    dsimp only [A] at hhalf ⊢
    omega
  have hMpos : 0 < M := by nlinarith only [hM2, sq_nonneg (A-1)]
  have hboundary : 0 < 2*M-C*(p-1) := by
    have hprod : 0 ≤ (q-1)*(q-3)*p :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (le_of_lt hp)
    have he : 2*M-C*(p-1) = (q-1)*(q-3)*p+2 := by
      rw [hM2]
      dsimp only [A, C]
      ring
    omega

  -- Only integer division bookkeeping; the ball counts are imported unchanged.
  have halfCap (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ho : Odd (a*b)) :
      2*((((a.toNat*b.toNat+1)/2 : ℕ) : ℤ)) = a*b+1 := by
    have hc : ((a.toNat*b.toNat+1 : ℕ) : ℤ) = a*b+1 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]
    have hdZ : (2 : ℤ) ∣ ((a.toNat*b.toNat+1 : ℕ) : ℤ) := by
      rw [hc]
      exact (ho.add_odd odd_one).two_dvd
    have hdN : (2 : ℕ) ∣ a.toNat*b.toNat+1 := by exact_mod_cast hdZ
    have hn := Nat.mul_div_cancel' hdN
    have hz : 2*((((a.toNat*b.toNat+1)/2 : ℕ) : ℤ)) =
        ((a.toNat*b.toNat+1 : ℕ) : ℤ) := by exact_mod_cast hn
    exact hz.trans hc
  have hgap_data (r : ℕ) (hr : r ≤ s) :
      let δ : ℤ := p*m-(2*(r : ℤ)+1)
      0 ≤ δ ∧ Even δ ∧
        (q*p ≤ δ → gap r = 0) ∧
        (p ≤ δ → δ < q*p → 2*gap r = (q*p-δ)^2+1) ∧
        (δ < p → 2*gap r = (q-1)^2*p*δ) := by
    let δ : ℤ := p*m-(2*(r : ℤ)+1)
    change 0 ≤ δ ∧ Even δ ∧
      (q*p ≤ δ → gap r = 0) ∧
      (p ≤ δ → δ < q*p → 2*gap r = (q*p-δ)^2+1) ∧
      (δ < p → 2*gap r = (q-1)^2*p*δ)
    have hrZ : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast hr
    have hδeq : δ = 2*((s : ℤ)-(r : ℤ)) := by dsimp only [δ]; omega
    have hδ : 0 ≤ δ := by omega
    have hδeven : Even δ := ⟨(s : ℤ)-(r : ℤ), by omega⟩
    have hwidth (a : ℤ) : 2*(r : ℤ)-p*(m-a)+1 = a*p-δ := by
      dsimp only [δ]
      ring
    have h1 := hcount1 r hr
    have hq := hcountq r hr
    dsimp only at h1 hq
    simp only [hwidth, one_mul] at h1 hq
    have h1Z : (c1 r : ℤ) +
        ((((p-δ).toNat*(q^2*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          2*(r : ℤ)^2+2*(r : ℤ)+1 := by exact_mod_cast h1
    have hqZ : (cq r : ℤ) +
        ((((q*p-δ).toNat*(q*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          2*(r : ℤ)^2+2*(r : ℤ)+1 := by exact_mod_cast hq
    have hbalance : gap r =
        ((((q*p-δ).toNat*(q*p-δ).toNat+1)/2 : ℕ) : ℤ) -
        ((((p-δ).toNat*(q^2*p-δ).toNat+1)/2 : ℕ) : ℤ) := by
      dsimp only [gap]
      omega
    have hoq : Odd (q*p-δ) := (hqo.mul hpo).sub_even hδeven
    refine ⟨hδ, hδeven, ?_, ?_, ?_⟩
    · intro hlarge
      have hw1 : (p-δ).toNat = 0 := by omega
      have hwq : (q*p-δ).toNat = 0 := by omega
      rw [hbalance, hw1, hwq]
      norm_num
    · intro hmid hupper
      have hw1 : (p-δ).toNat = 0 := by omega
      have hcap := halfCap (q*p-δ) (q*p-δ) (by omega) (by omega) (hoq.mul hoq)
      rw [hw1] at hbalance
      simp only [zero_mul, zero_add, Nat.reduceDiv, Nat.cast_zero, sub_zero] at hbalance
      nlinarith only [hbalance, hcap]
    · intro hsmall
      have ho1 : Odd (p-δ) := hpo.sub_even hδeven
      have hoq2 : Odd (q^2*p-δ) := (hq2o.mul hpo).sub_even hδeven
      have hcap1 := halfCap (p-δ) (q^2*p-δ)
        (by omega) (by omega) (ho1.mul hoq2)
      have hcapq := halfCap (q*p-δ) (q*p-δ)
        (by omega) (by omega) (hoq.mul hoq)
      nlinarith only [hbalance, hcap1, hcapq]

  have hsmall_profile (r : ℕ) (hr : r ≤ s) :
      0 ≤ gap r ∧
      (0 < gap r ↔ p*(m-q)/2 ≤ (r : ℤ) ∧ r < s) ∧
      gap r ≤ M ∧
      (gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) := by
    let δ : ℤ := p*m-(2*(r : ℤ)+1)
    obtain ⟨hδ, hδeven, hlarge, hmid, hsmall⟩ := hgap_data r hr
    change 0 ≤ δ at hδ
    change Even δ at hδeven
    change q*p ≤ δ → gap r = 0 at hlarge
    change p ≤ δ → δ < q*p → 2*gap r = (q*p-δ)^2+1 at hmid
    change δ < p → 2*gap r = C*δ at hsmall
    have hδeq : δ = 2*((s : ℤ)-(r : ℤ)) := by dsimp only [δ]; omega
    have hstartRel : 2*((r : ℤ)-p*(m-q)/2) = q*p-δ-1 := by
      dsimp only [δ]
      nlinarith only [hstart2]
    have hpeakRel : 2*((r : ℤ)-(p*(m-1)/2-1)) = p+1-δ := by
      dsimp only [δ]
      nlinarith only [hpeak2]
    have hstrictRange : (0 < δ ∧ δ < q*p) ↔
        p*(m-q)/2 ≤ (r : ℤ) ∧ r < s := by omega
    have hpeakRange : δ = p+1 ↔ (r : ℤ) = p*(m-1)/2-1 := by omega
    by_cases hh : q*p ≤ δ
    · have hz := hlarge hh
      refine ⟨by omega, ?_, by omega, ?_⟩
      · rw [← hstrictRange]
        omega
      · rw [← hpeakRange]
        omega
    · have hupper : δ < q*p := by omega
      by_cases hm : p ≤ δ
      · have hparity : p+1 ≤ δ := by
          obtain ⟨a, ha⟩ := hpo
          obtain ⟨b, hb⟩ := hδeven
          omega
        have he := hmid hm hupper
        have hpos : 0 < gap r := by nlinarith only [he, sq_nonneg (q*p-δ)]
        have hright : 0 < 2*A+p-δ-1 := by omega
        have hprod : 0 ≤ (δ-p-1)*(2*A+p-δ-1) :=
          mul_nonneg (by omega) (le_of_lt hright)
        have hfactor : 2*M-((q*p-δ)^2+1) =
            (δ-p-1)*(2*A+p-δ-1) := by
          rw [hM2, hqp]
          ring
        have hbound : gap r ≤ M := by nlinarith only [he, hfactor, hprod]
        refine ⟨le_of_lt hpos, ?_, hbound, ?_⟩
        · rw [← hstrictRange]
          exact iff_of_true hpos ⟨by omega, hupper⟩
        · rw [← hpeakRange]
          constructor
          · intro hmax
            have hz : (δ-p-1)*(2*A+p-δ-1) = 0 := by
              nlinarith only [he, hfactor, hmax]
            rcases mul_eq_zero.mp hz with hleft | hrightzero
            · omega
            · omega
          · intro hpeak
            rw [hpeak] at he
            rw [hqp] at he
            nlinarith only [he, hM2]
      · have hδp : δ < p := by omega
        have he := hsmall hδp
        have hnonneg : 0 ≤ gap r := by
          have hprod := mul_nonneg (le_of_lt hCpos) hδ
          omega
        have hproduct : C*δ ≤ C*(p-1) :=
          mul_le_mul_of_nonneg_left (by omega) (le_of_lt hCpos)
        have hlt : gap r < M := by omega
        refine ⟨hnonneg, ?_, le_of_lt hlt, ?_⟩
        · rw [← hstrictRange]
          constructor
          · intro hpos
            have hδpos : 0 < δ := by
              by_contra hn
              have hz : δ = 0 := by omega
              rw [hz, mul_zero] at he
              omega
            exact ⟨hδpos, hupper⟩
          · rintro ⟨hδpos, _⟩
            have hprod := mul_pos hCpos hδpos
            omega
        · rw [← hpeakRange]
          constructor <;> intro h <;> omega

  -- Saturation uses the imported coverage for these same quotient maps.
  have hfull (r : ℕ) (hr : s ≤ r) :
      (c1 r : ℤ) = p^2*D ∧ (cq r : ℤ) = p^2*D := by
    constructor
    · have hcover : LeeCovers F1 (r : ℤ) := (hdiam1 r).2 hr
      have hball : (leeDiamond r).image f1 = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro g
        obtain ⟨z, hz, hFz⟩ := hcover g
        refine Finset.mem_image.mpr ⟨E z, ?_, ?_⟩
        · simp only [leeDiamond, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
          have hx := abs_le.mp (show |z 0| ≤ (r : ℤ) by
            linarith [abs_nonneg (z 1)])
          have hy := abs_le.mp (show |z 1| ≤ (r : ℤ) by
            linarith [abs_nonneg (z 0)])
          exact ⟨⟨hx, hy⟩, hz⟩
        · change F1 (E.symm (E z)) = g
          rw [E.symm_apply_apply]
          exact hFz
      calc
        (c1 r : ℤ) = (Fintype.card G1 : ℤ) := by
          dsimp only [c1]
          rw [hball, Finset.card_univ]
        _ = (Nat.card G1 : ℤ) := by rw [Nat.card_eq_fintype_card]
        _ = p^2*D := hcard1
    · have hcover : LeeCovers Fq (r : ℤ) := (hdiamq r).2 hr
      have hball : (leeDiamond r).image fq = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro g
        obtain ⟨z, hz, hFz⟩ := hcover g
        refine Finset.mem_image.mpr ⟨E z, ?_, ?_⟩
        · simp only [leeDiamond, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
          have hx := abs_le.mp (show |z 0| ≤ (r : ℤ) by
            linarith [abs_nonneg (z 1)])
          have hy := abs_le.mp (show |z 1| ≤ (r : ℤ) by
            linarith [abs_nonneg (z 0)])
          exact ⟨⟨hx, hy⟩, hz⟩
        · change Fq (E.symm (E z)) = g
          rw [E.symm_apply_apply]
          exact hFz
      calc
        (cq r : ℤ) = (Fintype.card Gq : ℤ) := by
          dsimp only [cq]
          rw [hball, Finset.card_univ]
        _ = (Nat.card Gq : ℤ) := by rw [Nat.card_eq_fintype_card]
        _ = p^2*D := hcardq
  have hprofile (r : ℕ) :
      cq r ≤ c1 r ∧
      (cq r < c1 r ↔ p*(m-q)/2 ≤ (r : ℤ) ∧ r < s) ∧
      gap r ≤ M ∧
      (gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) := by
    by_cases hr : r ≤ s
    · obtain ⟨hnonneg, hstrict, hbound, he⟩ := hsmall_profile r hr
      have hle : cq r ≤ c1 r := by dsimp only [gap] at hnonneg; omega
      have hlt : cq r < c1 r ↔ 0 < gap r := by dsimp only [gap]; omega
      exact ⟨hle, hlt.trans hstrict, hbound, he⟩
    · have hsr : s ≤ r := by omega
      obtain ⟨h1full, hqfull⟩ := hfull r hsr
      have hcards : c1 r = cq r := by omega
      have hzero : gap r = 0 := by dsimp only [gap]; omega
      have hsrZ : (s : ℤ) ≤ (r : ℤ) := by exact_mod_cast hsr
      refine ⟨by omega, ?_, by omega, ?_⟩
      · constructor <;> intro h <;> omega
      · constructor <;> intro h <;> omega
  have hpeakNonneg : 0 ≤ p*(m-1)/2-1 := by
    have hprod : 30 ≤ p*(m-1) := by
      calc
        30 = 3*10 := by norm_num
        _ ≤ p*10 := by omega
        _ ≤ p*(m-1) := mul_le_mul_of_nonneg_left (by omega) (le_of_lt hp)
    omega
  let rmax : ℕ := (p*(m-1)/2-1).toNat
  have hrmaxCast : (rmax : ℤ) = p*(m-1)/2-1 := Int.toNat_of_nonneg hpeakNonneg
  have hmaxUnique : ∃! r : ℕ, gap r = M := by
    refine ⟨rmax, (hprofile rmax).2.2.2.mpr hrmaxCast, ?_⟩
    intro r hr
    have hrCast := (hprofile r).2.2.2.mp hr
    omega
  have hdeltaM : p*m-(2*((s-1 : ℕ) : ℤ)+1) = 2 := by
    nlinarith only [hs, hsm]
  have hlow := (hgap_data (s-1) (Nat.sub_le s 1)).2.2.2.2
  rw [hdeltaM] at hlow
  have hdiff : gap (s-1) = (q-1)^2*p := by
    have he := hlow (by omega)
    omega
  have hmarked : ¬ ∃ e : G1 ≃+ Gq,
      e (F1 ![1, 0]) = Fq ![1, 0] ∧
      e (F1 ![0, 1]) = Fq ![0, 1] := by
    rintro ⟨e, he0, he1⟩
    have hcoords (z : Plane) :
        z = z 0 • ![(1 : ℤ), 0]+z 1 • ![(0 : ℤ), 1] := by
      ext i
      fin_cases i <;> simp
    have heF (z : Plane) : e (F1 z) = Fq z := by
      have h1lin := congrArg (fun w : Plane => e (F1 w)) (hcoords z)
      have hqlin := congrArg (fun w : Plane => Fq w) (hcoords z)
      simp only [map_add, map_zsmul] at h1lin hqlin
      rw [h1lin, he0, he1, ← hqlin]
    have hef (z : ℤ × ℤ) : e (f1 z) = fq z := heF (E.symm z)
    have himage : ((leeDiamond (s-1)).image f1).image e =
        (leeDiamond (s-1)).image fq := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z _hz
      exact hef z
    have hcards : ((leeDiamond (s-1)).image f1).card =
        ((leeDiamond (s-1)).image fq).card := by
      rw [← himage, Finset.card_image_of_injective _ e.injective]
    have hzero : gap (s-1) = 0 := by
      dsimp only [gap, c1, cq]
      rw [hcards]
      exact sub_self _
    change 0 < (q-1)^2*p at hCpos
    omega
  refine ⟨e1, eq, ?_, ?_, hnoncyclic, hdiam1, hdiamq,
    (fun r => ⟨(hprofile r).1, (hprofile r).2.1⟩), hgap_data, hfull,
    (fun r => (hprofile r).2.2.1), (fun r => (hprofile r).2.2.2),
    hpeakNonneg, hmaxUnique, hdiff, hmarked⟩
  · intro z
    have he := he1 z
    simp only [neg_one_mul, one_mul] at he
    exact he
  · intro z
    exact heq z

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementGrowth
