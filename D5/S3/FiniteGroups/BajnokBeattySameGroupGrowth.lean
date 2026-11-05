/- GID: D5/S3/FiniteGroups/BajnokBeattySameGroupGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySameGroupGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Same finite group and diameter with sharply different growth. -/

import D5.S3.FiniteGroups.BajnokBeattyAsymmetricGrowth

/-!
proof_shape: same_group_coordinate_descent: content.
proof_shape: same_group_different_growth: content.
admission_basis: escape-witness.
escape_witness: explicit unimodular coordinate descent identifies both actual
quotients with one noncyclic product. The live gap calculation establishes
all-radius order and the unique discrete maximum, which the imported family
count does not assert. No primality, counting or covering hypothesis is added.
The descent is consumed by same_group_different_growth and the square-displacement extension.
No literature novelty or open-problem claim is made.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth

open BajnokBeattyAsymmetricGrowth BajnokBeattyExtremalGrowth
open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity
open scoped Classical

theorem same_group_coordinate_descent
    (p D x y u v alpha beta : ℤ) (v1 v2 : Plane)
    (hp : 0 < p) (hD : 0 < D)
    (hbez : alpha*x+beta*y = 1) (hdet : x*v-y*u = -D)
    (hv1 : v1 = ![p*x, p*y]) (hv2 : v2 = ![p*u, p*v])
    (hcard : (Nat.card (Plane ⧸
      Submodule.span ℤ (Set.range ![v1, v2])) : ℤ) = p^2*D) :
    let K : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1, v2])
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    ∃ e : (Plane ⧸ K) ≃+ H, ∀ z : Plane,
      e (K.mkQ z) =
        (((alpha*z 0+beta*z 1 : ℤ) : ZMod p.natAbs),
          ((-y*z 0+x*z 1 : ℤ) : ZMod (p*D).natAbs)) := by
  classical
  let K : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v1, v2])
  let G := Plane ⧸ K
  let H := ZMod p.natAbs × ZMod (p*D).natAbs
  let Phi : Plane →+ H :=
    { toFun := fun z =>
        (((alpha*z 0+beta*z 1 : ℤ) : ZMod p.natAbs),
          ((-y*z 0+x*z 1 : ℤ) : ZMod (p*D).natAbs))
      map_zero' := by
        apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply,
          mul_zero, add_zero, Int.cast_zero]
      map_add' := by
        intro z w
        apply Prod.ext
        · change ((alpha*(z 0+w 0)+beta*(z 1+w 1) : ℤ) : ZMod p.natAbs) =
            ((alpha*z 0+beta*z 1 : ℤ) : ZMod p.natAbs) +
            ((alpha*w 0+beta*w 1 : ℤ) : ZMod p.natAbs)
          rw [← Int.cast_add]
          congr 1
          ring
        · change ((-y*(z 0+w 0)+x*(z 1+w 1) : ℤ) : ZMod (p*D).natAbs) =
            ((-y*z 0+x*z 1 : ℤ) : ZMod (p*D).natAbs) +
            ((-y*w 0+x*w 1 : ℤ) : ZMod (p*D).natAbs)
          rw [← Int.cast_add]
          congr 1
          ring }
  have hpzero : (p : ZMod p.natAbs) = 0 := by
    apply (CharP.intCast_eq_zero_iff (ZMod p.natAbs) p.natAbs p).mpr
    simpa only [Int.natCast_natAbs, abs_of_pos hp] using (dvd_rfl : p ∣ p)
  have hpDzero : ((p*D : ℤ) : ZMod (p*D).natAbs) = 0 := by
    apply (CharP.intCast_eq_zero_iff
      (ZMod (p*D).natAbs) (p*D).natAbs (p*D)).mpr
    simpa only [Int.natCast_natAbs, abs_of_pos (mul_pos hp hD)] using
      (dvd_rfl : p*D ∣ p*D)
  have hPhi1 : Phi v1 = 0 := by
    rw [hv1]
    apply Prod.ext
    · change ((alpha*(p*x)+beta*(p*y) : ℤ) : ZMod p.natAbs) = 0
      have he : alpha*(p*x)+beta*(p*y) = p := by
        calc
          _ = p*(alpha*x+beta*y) := by ring
          _ = p := by rw [hbez]; ring
      rw [he]
      exact hpzero
    · change ((-y*(p*x)+x*(p*y) : ℤ) : ZMod (p*D).natAbs) = 0
      have he : -y*(p*x)+x*(p*y) = 0 := by ring
      simp only [he, Int.cast_zero]
  have hPhi2 : Phi v2 = 0 := by
    rw [hv2]
    apply Prod.ext
    · change ((alpha*(p*u)+beta*(p*v) : ℤ) : ZMod p.natAbs) = 0
      have he : alpha*(p*u)+beta*(p*v) = p*(alpha*u+beta*v) := by ring
      rw [he, Int.cast_mul, hpzero, zero_mul]
    · change ((-y*(p*u)+x*(p*v) : ℤ) : ZMod (p*D).natAbs) = 0
      have he : -y*(p*u)+x*(p*v) = -(p*D) := by
        calc
          _ = p*(x*v-y*u) := by ring
          _ = -(p*D) := by rw [hdet]; ring
      rw [he, Int.cast_neg, hpDzero, neg_zero]
  have hPhiK : K ≤ Phi.toIntLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    change Phi (![v1, v2] i) = 0
    fin_cases i
    · exact hPhi1
    · exact hPhi2
  let qPhi : G →+ H := (K.liftQ Phi.toIntLinearMap hPhiK).toAddMonoidHom
  have hsurj : Function.Surjective qPhi := by
    intro g
    obtain ⟨A, hA⟩ := ZMod.intCast_surjective g.1
    obtain ⟨B, hB⟩ := ZMod.intCast_surjective g.2
    refine ⟨K.mkQ ![x*A-beta*B, y*A+alpha*B], ?_⟩
    change Phi ![x*A-beta*B, y*A+alpha*B] = g
    apply Prod.ext
    · change ((alpha*(x*A-beta*B)+beta*(y*A+alpha*B) : ℤ) :
          ZMod p.natAbs) = g.1
      have he : alpha*(x*A-beta*B)+beta*(y*A+alpha*B) = A := by
        calc
          _ = (alpha*x+beta*y)*A := by ring
          _ = A := by rw [hbez]; ring
      rw [he]
      exact hA
    · change ((-y*(x*A-beta*B)+x*(y*A+alpha*B) : ℤ) :
          ZMod (p*D).natAbs) = g.2
      have he : -y*(x*A-beta*B)+x*(y*A+alpha*B) = B := by
        calc
          _ = (alpha*x+beta*y)*B := by ring
          _ = B := by rw [hbez]; ring
      rw [he]
      exact hB
  have hcardG : (Nat.card G : ℤ) = p^2*D := hcard
  have hpos : 0 < p^2*D := mul_pos (sq_pos_of_pos hp) hD
  letI : Finite G := Nat.finite_of_card_ne_zero (by
    intro hz
    rw [hz] at hcardG
    omega)
  have hcardH : (Nat.card H : ℤ) = p^2*D := by
    simp only [H, Nat.card_prod, Nat.card_zmod, Nat.cast_mul,
      Int.natCast_natAbs, abs_of_pos hp, abs_of_pos (mul_pos hp hD)]
    ring
  have hcardEq : Nat.card G = Nat.card H := by
    exact_mod_cast (hcardG.trans hcardH.symm)
  have hbij : Function.Bijective qPhi :=
    (Nat.bijective_iff_surjective_and_card qPhi).mpr ⟨hsurj, hcardEq⟩
  refine ⟨AddEquiv.ofBijective qPhi hbij, ?_⟩
  intro z
  rfl

/-- The actual marked quotients for (a,b)=(1,9) and (3,3) have the same
underlying noncyclic group and exact signed diameter. Their complete growth
profiles are ordered, strictly precisely on the stated interval. The integer
ball-cardinality gap has maximum 2*p^2-2*p+1 at exactly one natural radius.
Both balls have order p^2*D from radius s onwards; the penultimate difference
is 4*p. The explicit equivalences retain the Bezout rows (-1,1) and (t,1-t).
No covering, finiteness, primality, or symbolic count is assumed. -/
theorem same_group_different_growth (p t : ℤ)
    (hp3 : 3 ≤ p) (hpo : Odd p) (ht : 2 ≤ t) :
    let m : ℤ := 6*t-1
    let D : ℤ := (m^2-9)/2
    let H := ZMod p.natAbs × ZMod (p*D).natAbs
    let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
    let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
    let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
    let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
    let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
    let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
    let G19 := Plane ⧸ K19
    let G33 := Plane ⧸ K33
    let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
    let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
    let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
    let f19 : (ℤ × ℤ) →+ G19 := F19.comp E.symm.toLinearMap.toAddMonoidHom
    let f33 : (ℤ × ℤ) →+ G33 := F33.comp E.symm.toLinearMap.toAddMonoidHom
    let s : ℕ := ((p*m-1)/2).toNat
    let c19 : ℕ → ℕ := fun r => ((leeDiamond r).image f19).card
    let c33 : ℕ → ℕ := fun r => ((leeDiamond r).image f33).card
    let gap : ℕ → ℤ := fun r => (c19 r : ℤ)-(c33 r : ℤ)
    ∃ (e19 : G19 ≃+ H) (e33 : G33 ≃+ H),
      (∀ z : Plane, e19 (F19 z) =
        (((-z 0+z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t)*z 0+(3*t-1)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      (∀ z : Plane, e33 (F33 z) =
        (((t*z 0+(1-t)*z 1 : ℤ) : ZMod p.natAbs),
          ((-(3*t+1)*z 0+(3*t-2)*z 1 : ℤ) : ZMod (p*D).natAbs))) ∧
      ¬ IsAddCyclic H ∧
      (∀ R : ℕ, LeeCovers F19 (R : ℤ) ↔ s ≤ R) ∧
      (∀ R : ℕ, LeeCovers F33 (R : ℤ) ↔ s ≤ R) ∧
      (∀ r : ℕ, c33 r ≤ c19 r ∧
        (c33 r < c19 r ↔ p*(m-3)/2 ≤ (r : ℤ) ∧ r < s)) ∧
      (∀ r : ℕ, s ≤ r →
        (c19 r : ℤ) = p^2*D ∧ (c33 r : ℤ) = p^2*D) ∧
      (∀ r : ℕ, gap r ≤ 2*p^2-2*p+1) ∧
      (∀ r : ℕ, gap r = 2*p^2-2*p+1 ↔
        (r : ℤ) = p*(m-1)/2-1) ∧
      (∃! r : ℕ, gap r = 2*p^2-2*p+1) ∧
      (((leeDiamond (s-1)).image f19).card : ℤ) -
        (((leeDiamond (s-1)).image f33).card : ℤ) = 4*p ∧
      ¬ ∃ q : G19 ≃+ G33,
        q (F19 ![1, 0]) = F33 ![1, 0] ∧
        q (F19 ![0, 1]) = F33 ![0, 1] := by
  classical
  let m : ℤ := 6*t-1
  let D : ℤ := (m^2-9)/2
  let H := ZMod p.natAbs × ZMod (p*D).natAbs
  let v119 : Plane := ![p*(m-1)/2, p*(m+1)/2]
  let v219 : Plane := ![p*(m-9)/2, -(p*(m+9)/2)]
  let v133 : Plane := ![p*(m-3)/2, p*(m+3)/2]
  let v233 : Plane := ![p*(m-3)/2, -(p*(m+3)/2)]
  let K19 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v119, v219])
  let K33 : Submodule ℤ Plane := Submodule.span ℤ (Set.range ![v133, v233])
  let G19 := Plane ⧸ K19
  let G33 := Plane ⧸ K33
  let F19 : Plane →+ G19 := K19.mkQ.toAddMonoidHom
  let F33 : Plane →+ G33 := K33.mkQ.toAddMonoidHom
  let E : Plane ≃ₗ[ℤ] (ℤ × ℤ) := LinearEquiv.finTwoArrow ℤ ℤ
  let f19 : (ℤ × ℤ) →+ G19 := F19.comp E.symm.toLinearMap.toAddMonoidHom
  let f33 : (ℤ × ℤ) →+ G33 := F33.comp E.symm.toLinearMap.toAddMonoidHom
  let s : ℕ := ((p*m-1)/2).toNat
  let c19 : ℕ → ℕ := fun r => ((leeDiamond r).image f19).card
  let c33 : ℕ → ℕ := fun r => ((leeDiamond r).image f33).card
  let gap : ℕ → ℤ := fun r => (c19 r : ℤ)-(c33 r : ℤ)
  have hp : 0 < p := by omega
  have hm11 : 11 ≤ m := by dsimp [m]; omega
  have hmo : Odd m := ⟨3*t-1, by dsimp [m]; ring⟩
  have half_exact (c d : ℤ) (h : c = 2*d) : c/2 = d := by omega
  have hDpoly : D = 18*t^2-6*t-4 := by
    apply half_exact
    dsimp [m]
    ring
  have hD2 : 2*D = m^2-9 := by
    rw [hDpoly]
    dsimp [m]
    ring
  have hDpos : 0 < D := by
    rw [hDpoly]
    nlinarith [sq_nonneg (t-2)]
  have hhalfCard : p^2*(m^2-9)/2 = p^2*D := by
    apply half_exact
    rw [← hD2]
    ring
  obtain ⟨hf19, hn19, hc19, hcount19, _hcov19, _hncov19, hdiam19⟩ :=
    asymmetric_quotient_growth p m 1 9 hp3 hpo hmo
      (by decide) (by decide) (by norm_num) (by omega) (by norm_num) (by omega)
  obtain ⟨hf33, _hn33, hc33, hcount33, _hcov33, _hncov33, hdiam33⟩ :=
    asymmetric_quotient_growth p m 3 3 hp3 hpo hmo
      (by decide) (by decide) (by norm_num) (by omega) (by norm_num) (by omega)
  have hcard19 : (Nat.card G19 : ℤ) = p^2*D := by
    calc
      _ = p^2*(m^2-9)/2 := by simpa only [one_mul] using hc19
      _ = p^2*D := hhalfCard
  have hcard33 : (Nat.card G33 : ℤ) = p^2*D := by
    calc
      _ = p^2*(m^2-9)/2 := by
        simpa only [show (3 : ℤ)*3 = 9 by norm_num] using hc33
      _ = p^2*D := hhalfCard
  have hv119 : v119 = ![p*(3*t-1), p*(3*t)] := by
    ext i
    fin_cases i
    · change p*(m-1)/2 = p*(3*t-1)
      apply half_exact
      dsimp [m]
      ring
    · change p*(m+1)/2 = p*(3*t)
      apply half_exact
      dsimp [m]
      ring
  have hv219 : v219 = ![p*(3*t-5), p*(-(3*t+4))] := by
    ext i
    fin_cases i
    · change p*(m-9)/2 = p*(3*t-5)
      apply half_exact
      dsimp [m]
      ring
    · change -(p*(m+9)/2) = p*(-(3*t+4))
      have he : p*(m+9)/2 = p*(3*t+4) := by
        apply half_exact
        dsimp [m]
        ring
      rw [he]
      ring
  have hv133 : v133 = ![p*(3*t-2), p*(3*t+1)] := by
    ext i
    fin_cases i
    · change p*(m-3)/2 = p*(3*t-2)
      apply half_exact
      dsimp [m]
      ring
    · change p*(m+3)/2 = p*(3*t+1)
      apply half_exact
      dsimp [m]
      ring
  have hv233 : v233 = ![p*(3*t-2), p*(-(3*t+1))] := by
    ext i
    fin_cases i
    · change p*(m-3)/2 = p*(3*t-2)
      apply half_exact
      dsimp [m]
      ring
    · change -(p*(m+3)/2) = p*(-(3*t+1))
      have he : p*(m+3)/2 = p*(3*t+1) := by
        apply half_exact
        dsimp [m]
        ring
      rw [he]
      ring
  obtain ⟨e19, he19⟩ := same_group_coordinate_descent
    p D (3*t-1) (3*t) (3*t-5) (-(3*t+4)) (-1) 1 v119 v219 hp hDpos
    (by ring) (by rw [hDpoly]; ring) hv119 hv219 hcard19
  obtain ⟨e33, he33⟩ := same_group_coordinate_descent
    p D (3*t-2) (3*t+1) (3*t-2) (-(3*t+1)) t (1-t) v133 v233 hp hDpos
    (by ring) (by rw [hDpoly]; ring) hv133 hv233 hcard33
  have hnoncyclic : ¬ IsAddCyclic H := by
    intro hcyclic
    letI : IsAddCyclic H := hcyclic
    exact hn19 (isAddCyclic_of_surjective e19.symm.toAddMonoidHom e19.symm.surjective)

  -- Install only the finiteness already proved for the actual quotients.
  letI : Finite G19 := hf19
  letI : Finite G33 := hf33
  letI : Fintype G19 := Fintype.ofFinite G19
  letI : Fintype G33 := Fintype.ofFinite G33
  have hsZ : 2*((p*m-1)/2) = p*m-1 := by
    have hd := ((hpo.mul hmo).sub_odd odd_one).two_dvd
    simpa only [mul_comm] using Int.ediv_mul_cancel hd
  have hpm : 33 ≤ p*m := by
    have hprod : 0 ≤ (p-3)*(m-11) :=
      mul_nonneg (by omega) (by omega)
    nlinarith only [hp3, hm11, hprod]
  have hsCast : (s : ℤ) = (p*m-1)/2 := Int.toNat_of_nonneg (by omega)
  have hs : 2*(s : ℤ)+1 = p*m := by omega
  have hspos : 1 ≤ s := by omega
  have hsm : ((s-1 : ℕ) : ℤ) = (s : ℤ)-1 := by omega
  have hstartHalf : p*(m-3)/2 = p*(3*t-2) := by
    apply half_exact
    dsimp [m]
    ring
  have hpeakHalf : p*(m-1)/2 = p*(3*t-1) := by
    apply half_exact
    dsimp [m]
    ring
  have hstart2 : 2*(p*(m-3)/2) = p*(m-3) := by
    rw [hstartHalf]
    dsimp [m]
    ring
  have hpeak2 : 2*(p*(m-1)/2-1) = p*(m-1)-2 := by
    rw [hpeakHalf]
    dsimp [m]
    ring
  let M : ℤ := 2*p^2-2*p+1
  have hMpos : 0 < M := by
    dsimp only [M]
    nlinarith only [hp3, sq_nonneg (p-1)]
  have hpeakLt : p*(m-1)/2-1 < (s : ℤ) := by
    nlinarith only [hs, hpeak2, hp3]

  -- Derive all three regimes from the two ACTUAL family counts.
  have hgap_data (r : ℕ) (hr : r ≤ s) :
      let δ : ℤ := p*m-(2*(r : ℤ)+1)
      0 ≤ δ ∧ Even δ ∧
        (3*p ≤ δ → gap r = 0) ∧
        (p ≤ δ → δ < 3*p → 2*gap r = (3*p-δ)^2+1) ∧
        (δ < p → gap r = 2*p*δ) := by
    let δ : ℤ := p*m-(2*(r : ℤ)+1)
    change 0 ≤ δ ∧ Even δ ∧
      (3*p ≤ δ → gap r = 0) ∧
      (p ≤ δ → δ < 3*p → 2*gap r = (3*p-δ)^2+1) ∧
      (δ < p → gap r = 2*p*δ)
    have hrZ : (r : ℤ) ≤ (s : ℤ) := by exact_mod_cast hr
    have hδeq : δ = 2*((s : ℤ)-(r : ℤ)) := by dsimp [δ]; omega
    have hδ : 0 ≤ δ := by omega
    have hδeven : Even δ := ⟨(s : ℤ)-(r : ℤ), by omega⟩
    have hwidth (a : ℤ) : 2*(r : ℤ)-p*(m-a)+1 = a*p-δ := by
      dsimp [δ]
      ring
    have h19 := hcount19 r hr
    have h33 := hcount33 r hr
    dsimp only at h19 h33
    simp only [hwidth, one_mul] at h19 h33
    have h19Z : (c19 r : ℤ) +
        ((((p-δ).toNat*(9*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          2*(r : ℤ)^2+2*(r : ℤ)+1 := by exact_mod_cast h19
    have h33Z : (c33 r : ℤ) +
        ((((3*p-δ).toNat*(3*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          2*(r : ℤ)^2+2*(r : ℤ)+1 := by exact_mod_cast h33
    have hbalance : gap r =
        ((((3*p-δ).toNat*(3*p-δ).toNat+1)/2 : ℕ) : ℤ) -
        ((((p-δ).toNat*(9*p-δ).toNat+1)/2 : ℕ) : ℤ) := by
      dsimp only [gap]
      omega
    have ho3 : Odd (3*p-δ) :=
      ((by decide : Odd (3 : ℤ)).mul hpo).sub_even hδeven
    refine ⟨hδ, hδeven, ?_, ?_, ?_⟩
    · intro hlarge
      have hw1 : (p-δ).toNat = 0 := by omega
      have hw3 : (3*p-δ).toNat = 0 := by omega
      rw [hbalance, hw1, hw3]
      norm_num
    · intro hmid hupper
      have hw1 : (p-δ).toNat = 0 := by omega
      have hcap : 2*((((3*p-δ).toNat*(3*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          (3*p-δ)*(3*p-δ)+1 := by
        have hn : (((3*p-δ).toNat*(3*p-δ).toNat : ℕ) : ℤ) =
            (3*p-δ)*(3*p-δ) := by
          simp only [Nat.cast_mul, Int.toNat_of_nonneg (show 0 ≤ 3*p-δ by omega)]
        obtain ⟨k, hk⟩ := ho3.mul ho3
        omega
      rw [hw1] at hbalance
      simp only [zero_mul, zero_add, Nat.reduceDiv, Nat.cast_zero, sub_zero] at hbalance
      nlinarith only [hbalance, hcap]
    · intro hsmall
      have ho1 : Odd (p-δ) := hpo.sub_even hδeven
      have ho9 : Odd (9*p-δ) :=
        ((by decide : Odd (9 : ℤ)).mul hpo).sub_even hδeven
      have hcap19 : 2*((((p-δ).toNat*(9*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          (p-δ)*(9*p-δ)+1 := by
        have hn : (((p-δ).toNat*(9*p-δ).toNat : ℕ) : ℤ) =
            (p-δ)*(9*p-δ) := by
          rw [Nat.cast_mul, Int.toNat_of_nonneg (by omega),
            Int.toNat_of_nonneg (by omega)]
        obtain ⟨k, hk⟩ := ho1.mul ho9
        omega
      have hcap33 : 2*((((3*p-δ).toNat*(3*p-δ).toNat+1)/2 : ℕ) : ℤ) =
          (3*p-δ)*(3*p-δ)+1 := by
        have hn : (((3*p-δ).toNat*(3*p-δ).toNat : ℕ) : ℤ) =
            (3*p-δ)*(3*p-δ) := by
          simp only [Nat.cast_mul, Int.toNat_of_nonneg (show 0 ≤ 3*p-δ by omega)]
        obtain ⟨k, hk⟩ := ho3.mul ho3
        omega
      nlinarith only [hbalance, hcap19, hcap33]

  have hsmall_profile (r : ℕ) (hr : r ≤ s) :
      0 ≤ gap r ∧
      (0 < gap r ↔ p*(m-3)/2 ≤ (r : ℤ) ∧ r < s) ∧
      gap r ≤ M ∧
      (gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) := by
    let δ : ℤ := p*m-(2*(r : ℤ)+1)
    obtain ⟨hδ, hδeven, hlarge, hmid, hsmall⟩ := hgap_data r hr
    change 0 ≤ δ at hδ
    change Even δ at hδeven
    change 3*p ≤ δ → gap r = 0 at hlarge
    change p ≤ δ → δ < 3*p → 2*gap r = (3*p-δ)^2+1 at hmid
    change δ < p → gap r = 2*p*δ at hsmall
    have hδeq : δ = 2*((s : ℤ)-(r : ℤ)) := by dsimp [δ]; omega
    have hstartRel : 2*((r : ℤ)-p*(m-3)/2) = 3*p-δ-1 := by
      dsimp [δ]
      nlinarith only [hstart2]
    have hpeakRel : 2*((r : ℤ)-(p*(m-1)/2-1)) = p+1-δ := by
      dsimp [δ]
      nlinarith only [hpeak2]
    have hstrictRange : (0 < δ ∧ δ < 3*p) ↔
        p*(m-3)/2 ≤ (r : ℤ) ∧ r < s := by omega
    have hpeakRange : δ = p+1 ↔ (r : ℤ) = p*(m-1)/2-1 := by omega
    by_cases hh : 3*p ≤ δ
    · have hz := hlarge hh
      refine ⟨by omega, ?_, by omega, ?_⟩
      · rw [← hstrictRange]
        omega
      · rw [← hpeakRange]
        omega
    · have hupper : δ < 3*p := by omega
      by_cases hm : p ≤ δ
      · have hparity : p+1 ≤ δ := by
          obtain ⟨a, ha⟩ := hpo
          obtain ⟨b, hb⟩ := hδeven
          omega
        have heq := hmid hm hupper
        have hpos : 0 < gap r := by
          nlinarith only [heq, sq_nonneg (3*p-δ)]
        have hprod : 0 ≤ (δ-p-1)*(5*p-δ-1) :=
          mul_nonneg (by omega) (by omega)
        have hbound : gap r ≤ M := by
          dsimp only [M]
          nlinarith only [heq, hprod]
        refine ⟨le_of_lt hpos, ?_, hbound, ?_⟩
        · rw [← hstrictRange]
          exact iff_of_true hpos ⟨by omega, hupper⟩
        · rw [← hpeakRange]
          constructor
          · intro hmax
            have hprodZero : (δ-p-1)*(5*p-δ-1) = 0 := by
              dsimp only [M] at hmax
              nlinarith only [heq, hmax]
            rcases mul_eq_zero.mp hprodZero with hleft | hright
            · omega
            · omega
          · intro hpeak
            rw [hpeak] at heq
            dsimp only [M]
            nlinarith only [heq]
      · have hδp : δ < p := by omega
        have heq := hsmall hδp
        have hnonneg : 0 ≤ gap r := by
          rw [heq]
          exact mul_nonneg (by omega) hδ
        have hproduct : 2*p*δ ≤ 2*p*(p-1) :=
          mul_le_mul_of_nonneg_left (by omega) (by omega)
        have hlt : gap r < M := by
          dsimp only [M]
          nlinarith only [heq, hproduct]
        refine ⟨hnonneg, ?_, le_of_lt hlt, ?_⟩
        · rw [← hstrictRange]
          constructor
          · intro hpos
            have hδpos : 0 < δ := by
              by_contra hn
              have hz : δ = 0 := by omega
              rw [hz, mul_zero] at heq
              omega
            exact ⟨hδpos, hupper⟩
          · rintro ⟨hδpos, _⟩
            rw [heq]
            exact mul_pos (by omega) hδpos
        · rw [← hpeakRange]
          constructor <;> intro h <;> omega

  -- Beyond the diameter use actual coverage and actual quotient order.
  have hfull (r : ℕ) (hr : s ≤ r) :
      (c19 r : ℤ) = p^2*D ∧ (c33 r : ℤ) = p^2*D := by
    constructor
    · have hcover : LeeCovers F19 (r : ℤ) := (hdiam19 r).2 hr
      have hball : (leeDiamond r).image f19 = Finset.univ := by
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
        · change F19 (E.symm (E z)) = g
          rw [E.symm_apply_apply]
          exact hFz
      calc
        (c19 r : ℤ) = (Fintype.card G19 : ℤ) := by
          dsimp only [c19]
          rw [hball, Finset.card_univ]
        _ = (Nat.card G19 : ℤ) := by rw [Nat.card_eq_fintype_card]
        _ = p^2*D := hcard19
    · have hcover : LeeCovers F33 (r : ℤ) := (hdiam33 r).2 hr
      have hball : (leeDiamond r).image f33 = Finset.univ := by
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
        · change F33 (E.symm (E z)) = g
          rw [E.symm_apply_apply]
          exact hFz
      calc
        (c33 r : ℤ) = (Fintype.card G33 : ℤ) := by
          dsimp only [c33]
          rw [hball, Finset.card_univ]
        _ = (Nat.card G33 : ℤ) := by rw [Nat.card_eq_fintype_card]
        _ = p^2*D := hcard33

  have hprofile (r : ℕ) :
      c33 r ≤ c19 r ∧
      (c33 r < c19 r ↔ p*(m-3)/2 ≤ (r : ℤ) ∧ r < s) ∧
      gap r ≤ M ∧
      (gap r = M ↔ (r : ℤ) = p*(m-1)/2-1) := by
    by_cases hr : r ≤ s
    · obtain ⟨hnonneg, hstrict, hbound, heq⟩ := hsmall_profile r hr
      have hle : c33 r ≤ c19 r := by
        dsimp only [gap] at hnonneg
        omega
      have hlt : c33 r < c19 r ↔ 0 < gap r := by
        dsimp only [gap]
        omega
      exact ⟨hle, hlt.trans hstrict, hbound, heq⟩
    · have hsr : s ≤ r := by omega
      obtain ⟨h19full, h33full⟩ := hfull r hsr
      have hcards : c19 r = c33 r := by omega
      have hzero : gap r = 0 := by dsimp only [gap]; omega
      have hsrZ : (s : ℤ) ≤ (r : ℤ) := by exact_mod_cast hsr
      refine ⟨by omega, ?_, by omega, ?_⟩
      · constructor <;> intro h <;> omega
      · constructor <;> intro h <;> omega

  have hpeakNonneg : 0 ≤ p*(m-1)/2-1 := by
    have hprodpos : 0 < p*(m-1) := mul_pos hp (by omega)
    omega
  let rmax : ℕ := (p*(m-1)/2-1).toNat
  have hrmaxCast : (rmax : ℤ) = p*(m-1)/2-1 := Int.toNat_of_nonneg hpeakNonneg
  have hmaxUnique : ∃! r : ℕ, gap r = M := by
    refine ⟨rmax, (hprofile rmax).2.2.2.mpr hrmaxCast, ?_⟩
    intro r hr
    have hrCast := (hprofile r).2.2.2.mp hr
    omega

  -- Reuse the same actual penultimate radius and feed its card obstruction.
  have hdeltaM : p*m-(2*((s-1 : ℕ) : ℤ)+1) = 2 := by
    nlinarith only [hs, hsm]
  have hlow := (hgap_data (s-1) (Nat.sub_le s 1)).2.2.2.2
  rw [hdeltaM] at hlow
  have hdiff : (((leeDiamond (s-1)).image f19).card : ℤ) -
      (((leeDiamond (s-1)).image f33).card : ℤ) = 4*p := by
    change gap (s-1) = 4*p
    have heq := hlow (by omega)
    nlinarith only [heq]

  -- An isomorphism of the marked pairs would identify every signed word.
  have hmarked : ¬ ∃ q : G19 ≃+ G33,
      q (F19 ![1, 0]) = F33 ![1, 0] ∧
      q (F19 ![0, 1]) = F33 ![0, 1] := by
    rintro ⟨q, hq0, hq1⟩
    have hcoords (z : Plane) :
        z = z 0 • ![(1 : ℤ), 0]+z 1 • ![(0 : ℤ), 1] := by
      ext i
      fin_cases i <;> simp
    have hqF (z : Plane) : q (F19 z) = F33 z := by
      have h19lin := congrArg (fun w : Plane => q (F19 w)) (hcoords z)
      have h33lin := congrArg (fun w : Plane => F33 w) (hcoords z)
      simp only [map_add, map_zsmul] at h19lin h33lin
      rw [h19lin, hq0, hq1, ← h33lin]
    have hqf (z : ℤ × ℤ) : q (f19 z) = f33 z := hqF (E.symm z)
    have himage : ((leeDiamond (s-1)).image f19).image q =
        (leeDiamond (s-1)).image f33 := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro z _hz
      exact hqf z
    have hcards : ((leeDiamond (s-1)).image f19).card =
        ((leeDiamond (s-1)).image f33).card := by
      rw [← himage, Finset.card_image_of_injective _ q.injective]
    have hcardsZ : (((leeDiamond (s-1)).image f19).card : ℤ) =
        (((leeDiamond (s-1)).image f33).card : ℤ) := by exact_mod_cast hcards
    omega
  refine ⟨e19, e33, ?_, ?_, hnoncyclic, hdiam19, hdiam33,
    (fun r => ⟨(hprofile r).1, (hprofile r).2.1⟩), hfull,
    (fun r => (hprofile r).2.2.1), (fun r => (hprofile r).2.2.2),
    hmaxUnique, hdiff, hmarked⟩
  · intro z
    have he := he19 z
    simp only [neg_one_mul, one_mul] at he
    exact he
  · intro z
    exact he33 z

end D5.S3.FiniteGroups.BajnokBeattySameGroupGrowth
