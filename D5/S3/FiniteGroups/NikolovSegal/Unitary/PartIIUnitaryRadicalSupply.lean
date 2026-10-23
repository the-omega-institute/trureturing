/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalSupply
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryRadicalTorus
import D5.S3.FiniteGroups.NikolovSegal.Unitary.PartIIUnitaryTorusSupply
set_option autoImplicit false
set_option maxHeartbeats 1800000
/-! Actual four-entry determinant-one unitary torus on V*. A generator
of F* is chosen once before every rank/target. Only the genuine radical
root ratios are separated, with cutoff Q>2q+2 independent of rank.
This proves the fixed-inner-action kernel of Proposition6.7; arbitrary
prescribed diagonal/field/graph tuples still require their normalization. -/
namespace NikolovSegal.PartIIUnitaryRadicalSupply
open Matrix PartIIUnitriangularLayers PartIIRadicalCoordinates
open PartIIUnitaryUpperTorus PartIIUnitaryRadicalTorus PartIIUnitaryTorusSupply
open UnitaryField
universe u
variable {F : Type u} [Field F] [Finite F] {k : ℕ}

private def weights (ι : RingAut F) (u : Fˣ) : Fin (k+4) → Fˣ :=
  Fin.cons u (Fin.cons u⁻¹ (Fin.snoc (Fin.snoc (fun _ : Fin k => 1)
    (involutionUnit ι u)) (involutionUnit ι u)⁻¹))
private theorem weights_product (ι : RingAut F) (u : Fˣ) : ∏ i, weights (k:=k) ι u i=1 := by
  simp [weights,Fin.prod_cons,Fin.prod_snoc,mul_assoc]
private theorem weights_entry (ι : RingAut F) (u : Fˣ) (i : Fin (k+4)) :
    weights ι u i=
      if i.val=0 then u else if i.val=1 then u⁻¹
      else if i.val=k+2 then involutionUnit ι u
      else if i.val=k+3 then (involutionUnit ι u)⁻¹ else 1 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · simp [weights]
  · simp [weights]
  · refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun t => ?_) j) j
    · simp [weights,Fin.val_succ,Fin.val_last]
    · simp [weights,Fin.val_succ,Fin.val_castSucc,Fin.val_last]
    · simp [weights,Fin.val_succ,Fin.val_castSucc,show t.val≠k by omega,
        show t.val≠k+1 by omega]

private theorem weights_unitary (ι : RingAut F) (hinv : Function.Involutive ι)
    (u : Fˣ) (i : Fin (k+4)) :
    ι (weights ι u i:F)*(weights ι u i.rev:F)=1 := by
  rw [weights_entry,weights_entry]
  by_cases h0 : i.val=0
  · have hr : i.rev.val=k+3 := by simp [Fin.val_rev,h0]
    simp [h0,hr,involutionUnit_val,Units.val_inv_eq_inv_val]
  · by_cases h1 : i.val=1
    · have hr : i.rev.val=k+2 := by simp [Fin.val_rev,h1]
      simp [h0,h1,hr,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀]
    · by_cases h2 : i.val=k+2
      · have hr : i.rev.val=1 := by simp [Fin.val_rev,h2]
        simp [h0,h1,h2,hr,involutionUnit_val,Units.val_inv_eq_inv_val,hinv (u:F)]
      · by_cases h3 : i.val=k+3
        · have hr : i.rev.val=0 := by simp [Fin.val_rev,h3]
          simp [h0,h1,h2,h3,hr,involutionUnit_val,Units.val_inv_eq_inv_val,map_inv₀,hinv (u:F)]
        · have hr0 : i.rev.val≠0 := by simp only [Fin.val_rev]; omega
          have hr1 : i.rev.val≠1 := by simp only [Fin.val_rev]; omega
          have hr2 : i.rev.val≠k+2 := by simp only [Fin.val_rev]; omega
          have hr3 : i.rev.val≠k+3 := by simp only [Fin.val_rev]; omega
          simp only [h0,h1,h2,h3,hr0,hr1,hr2,hr3,ite_false,Units.val_one,map_one,mul_one]

private def exponent (Q : ℕ) (i : Fin (k+4)) : ℤ :=
  if i.val=0 then 1 else if i.val=1 then -1
  else if i.val=k+2 then (Q:ℤ) else if i.val=k+3 then -(Q:ℤ) else 0
private theorem weights_power (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (u : Fˣ) (i : Fin (k+4)) :
    weights ι u i=u^exponent (Nat.card (fixedField ι)) i := by
  rw [weights_entry]
  simp only [exponent,involutionUnit_pow ι hinv hne]
  split_ifs <;> simp [zpow_neg,zpow_natCast]
private theorem exponent_bound (Q : ℕ) (hQ : 1≤Q) (i : Fin (k+4)) : |exponent Q i|≤Q := by
  unfold exponent
  split_ifs <;> simp <;> omega
private theorem exponent_active_ne (Q : ℕ) (hQ : 2<Q) (i j : Fin (k+4))
    (hij : i≠j) (ha : i=first ∨ j=last) : exponent Q i≠exponent Q j := by
  have hne : i.val≠j.val := fun he => hij (Fin.ext he)
  rcases ha with hi | hj
  · subst i
    simp only [first,Fin.val_zero] at hne
    simp only [exponent,first,Fin.val_zero,ite_true]
    split_ifs <;> omega
  · subst j
    have hi3 : i.val≠k+3 := by simpa only [last,Fin.val_last] using hne
    simp only [exponent,last,Fin.val_last,show k+3≠0 by omega,show k+3≠1 by omega,
      show k+3≠k+2 by omega,ite_false,ite_true]
    split_ifs <;> omega

private theorem weights_separate (ι : RingAut F) (hinv : Function.Involutive ι)
    (hne : ι≠RingEquiv.refl F) (q : ℕ) (hq : 0<q)
    (hQ : 2*q+2<Nat.card (fixedField ι)) :
    ∃ u : Fˣ, ∀ k s : ℕ, 0<s → s≤q →
      ∀ i j : Fin (k+4), i≠j → (i=first ∨ j=last) →
        (weights ι u i/weights ι u j)^s≠1 := by
  obtain ⟨u,hu⟩ := full_unit_simultaneous_avoidance ι hinv hne
  refine ⟨u,?_⟩
  intro k s hs hsq i j hij ha hp
  let Q := Nat.card (fixedField ι)
  have hQ2 : 2<Q := by dsimp only [Q]; omega
  have hen : exponent Q i-exponent Q j≠0 :=
    sub_ne_zero.mpr (exponent_active_ne Q hQ2 i j hij ha)
  have hes : (s:ℤ)≠0 := by omega
  have hb : |exponent Q i-exponent Q j|≤2*(Q:ℤ) := by
    have hd := abs_sub (exponent Q i) (exponent Q j)
    have hi := exponent_bound Q (by omega) i
    have hj := exponent_bound Q (by omega) j
    linarith
  have hlength : ((exponent Q i-exponent Q j)*(s:ℤ)).natAbs<Q^2-1 := by
    rw [← Nat.cast_lt (α:=ℤ),Int.natCast_natAbs,abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤s),
      Nat.cast_sub (by nlinarith : 1≤Q^2)]
    push_cast
    have hQz : 2*(q:ℤ)+2<Q := by exact_mod_cast hQ
    have hsqz : (s:ℤ)≤q := by exact_mod_cast hsq
    have hh := mul_le_mul_of_nonneg_right hb (by positivity : (0:ℤ)≤s)
    have hpos : (0:ℤ)≤Q := by positivity
    nlinarith
  apply hu _ (mul_ne_zero hen hes) hlength
  rw [weights_power ι hinv hne,weights_power ι hinv hne,div_eq_mul_inv,
    ← zpow_sub,← zpow_natCast,← zpow_mul] at hp
  exact hp

/-- A true UNIFORM radical fixed-inner-action result, all ranks k+4 and
every original positive divisor power s|q. The Q cutoff 2q+2 precedes
all groups/ranks, the same genuine determinant-one unitary h precedes
ALL s and ALL targets, and the witness lies in V*, including its corner.
No scalar PRODUCT or radical coverage premise is retained. This does
not yet handle arbitrary prescribed diagonal/field/graph automorphisms. -/
theorem actual_uniform_unitary_radical_fixed_torus (q : ℕ) (hq : 0<q)
    (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (hQ : 2*q+2<Nat.card (fixedField ι)) :
    ∀ k : ℕ, ∃ h : SpecialLinearGroup (Fin (k+4)) F,
      UnitaryField.adjoint ι h.val*antiDiagonal (F:=F) (k+4)*h.val=antiDiagonal (F:=F) (k+4) ∧
      ∀ s : ℕ, 0<s → s∣q →
        ∀ b : SpecialLinearGroup (Fin (k+4)) F,
          InRadical b →
          UnitaryField.adjoint ι b.val*antiDiagonal (F:=F) (k+4)*b.val=antiDiagonal (F:=F) (k+4) →
          ∃ x : SpecialLinearGroup (Fin (k+4)) F,
            InRadical x ∧
            UnitaryField.adjoint ι x.val*antiDiagonal (F:=F) (k+4)*x.val=antiDiagonal (F:=F) (k+4) ∧
            x⁻¹*h^s*x*(h^s)⁻¹=b := by
  obtain ⟨u,hu⟩ := weights_separate ι hinv hne q hq hQ
  intro k
  let w : Fin (k+4) → Fˣ := weights ι u
  let h := (radicalTorus% diagonalSL) w (weights_product ι u)
  have hh : steinberg ι h=h := (unitaryTorus% diagonal_fixed) ι w (weights_product ι u)
    (weights_unitary ι hinv u)
  refine ⟨h,(actual_steinberg_iff_hermitian ι hinv h).mp hh,?_⟩
  intro s hs hsq b hb hbu
  obtain ⟨h',hh',hh'u,hcover⟩ := actual_unitary_radical_regular_torus_values
    ι w (weights_product ι u) (weights_unitary ι hinv u) s
    (hu k s hs (Nat.le_of_dvd hq hsq))
  have he : h'=h := Subtype.ext hh'
  subst h'
  obtain ⟨x,hx,hxu,hxe⟩ := hcover b hb ((actual_steinberg_iff_hermitian ι hinv b).mpr hbu)
  exact ⟨x,hx,(actual_steinberg_iff_hermitian ι hinv x).mp hxu,hxe⟩
end NikolovSegal.PartIIUnitaryRadicalSupply
