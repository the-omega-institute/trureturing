/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalBoundaryCoprime
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalBoundaryCoprime
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Boundary coprimality of the divided outer determinant. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSWeightedLineSpecialization
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformVerticalSection
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
On the vertical critical-divisor branch where the singlet factor `h_(m-2)`
vanishes, the outer determinant must remain generically nonzero. Setting
`s = u = 0` and fixing the section parameter leaves a scalar times a monomial.
The pure powers in the specialized singlet factor exclude both coordinate
divisors. Homogeneity lifts relative primality back to the spectral ring.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalBoundaryCoprime

open MvPolynomial

noncomputable section

/-- Setting all variables outside the range of `f` to zero reflects relative
primality when the first polynomial has positive weights and survives.
Only the first polynomial needs to be weighted homogeneous. -/
theorem isRelPrime_of_killCompl {σ τ R : Type*} [CommRing R] [IsDomain R]
    {f : σ → τ} (hf : Function.Injective f) {w : τ → ℕ} (hw : ∀ i, w i ≠ 0)
    {p g : MvPolynomial τ R} {n : ℕ} (hp : p.IsWeightedHomogeneous w n)
    (hs : killCompl hf p ≠ 0) (hrel : IsRelPrime (killCompl hf p) (killCompl hf g)) :
    IsRelPrime p g := by
  intro d hdp hdg
  have hpne : p ≠ 0 := fun h => hs (by simp [h])
  obtain ⟨e, hd⟩ :=
    PeriodicMPSWeightedLineSpecialization.isWeightedHomogeneous_of_dvd hpne hp hdp
  have hu := hrel (map_dvd (killCompl hf) hdp) (map_dvd (killCompl hf) hdg)
  obtain ⟨c, hc, heq⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have hcoeff : d.coeff 0 = c := by
    simpa only [coeff_killCompl, Finsupp.mapDomain_zero, coeff_zero_C] using
      congrArg (fun p : MvPolynomial σ R => p.coeff 0) heq
  have hdegree : e = 0 := by
    simpa only [map_zero] using (hd (d := 0) (hcoeff.symm ▸ hc.ne_zero)).symm
  subst e
  have hconst : d = C (d.coeff 0) :=
    (weightedHomogeneousComponent_eq_self hd).symm.trans (weightedHomogeneousComponent_zero d hw)
  rw [hconst, hcoeff]
  exact hc.map C

section Boundary

variable {K : Type*} [Field K]

private theorem hsymm_homogeneous {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ) :
    (hsymm ι K n).IsHomogeneous n := by
  have hprod (s : Multiset ι) : ((s.map (X : ι → MvPolynomial ι K)).prod).IsHomogeneous s.card := by
    induction s using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one ι K
    | cons i s ih =>
      simpa only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Nat.add_comm] using
        (isHomogeneous_X K i).mul ih
  unfold hsymm
  apply IsHomogeneous.sum
  intro s _
  simpa only [s.property] using hprod s.val

private theorem aeval_hsymm_axis {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra K A] (j : ι) (x : A) (n : ℕ) :
    aeval (Pi.single j x) (hsymm ι K n) = x ^ n := by
  classical
  simp only [hsymm, map_sum, ← Multiset.prod_hom', aeval_X]
  rw [Finset.sum_eq_single (Sym.replicate n j)]
  · simp [Sym.coe_replicate]
  · intro s _ hs
    have h : ¬ ∀ i ∈ s, i = j := fun h => hs (Sym.eq_replicate.mpr h)
    push Not at h
    obtain ⟨i, hi, hij⟩ := h
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨i, hi, by simp [hij]⟩)
  · simp

private def survivingRoot : Fin 2 → Fin 5 := ![0, 2]

private theorem survivingRoot_injective : Function.Injective survivingRoot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [survivingRoot]

private theorem killCompl_survivingRoot :
    (killCompl (R := K) survivingRoot_injective) =
      aeval ![X (0 : Fin 2), 0, X (1 : Fin 2), 0, 0] := by
  apply algHom_ext
  intro i
  have hrange : Set.range survivingRoot = ({0, 2} : Set (Fin 5)) := by
    ext j
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      survivingRoot, Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
  have hX (j : Fin 2) :
      killCompl (R := K) survivingRoot_injective (X (survivingRoot j)) = X j := by
    rw [← rename_X, killCompl_rename_app]
  fin_cases i
  · simpa [survivingRoot] using hX 0
  · simp [killCompl, hrange]
  · simpa [survivingRoot] using hX 1
  · simp [killCompl, hrange]
  · simp [killCompl, hrange]

local notation "P" => MvPolynomial (Fin 5) K
local notation "B" => MvPolynomial (Fin 2) K
local notation "H" n => rename Fin.castSucc (hsymm (Fin 4) K n)
local notation "boundaryEval(" z ")" =>
  (aeval ![X (0 : Fin 2), 0, X (1 : Fin 2), 0, C z] : P →ₐ[K] B)

private theorem boundary_axis (z : K) (n : ℕ) (j : Fin 2) :
    aeval (Pi.single j (1 : K)) (boundaryEval(z) (H n)) = 1 := by
  rw [← AlgHom.comp_apply]
  have heq : ((aeval (Pi.single j (1 : K))).comp boundaryEval(z)) =
      aeval (fun i => (aeval (Pi.single j (1 : K))) (![X (0 : Fin 2), 0, X 1, 0, C z] i)) := by
    apply algHom_ext
    intro i
    simp
  rw [heq, aeval_rename]
  rw [show (fun i => (aeval (Pi.single j (1 : K))) (![X (0 : Fin 2), 0, X 1, 0, C z] i)) ∘
      (Fin.castSucc : Fin 4 → Fin 5) = Pi.single ((![0, 2] : Fin 2 → Fin 4) j) (1 : K) by
    funext i
    fin_cases i <;> fin_cases j <;> simp]
  rw [aeval_hsymm_axis, one_pow]

/-- For the four-root complete homogeneous singlet factor, the boundary
`s = u = 0, q = z` suffices whenever the other polynomial restricts to a
nonzero scalar times a monomial in `r,t`. The section parameter may occur
in that polynomial. -/
theorem hsymm_isRelPrime_of_boundary_monomial (n : ℕ) (g : P) (z c : K)
    (hc : c ≠ 0) (a b : ℕ)
    (hg : boundaryEval(z) g = C c * (X (0 : Fin 2)) ^ a * (X (1 : Fin 2)) ^ b) :
    IsRelPrime (H n) g := by
  -- Translate q so that killing it evaluates at z. The singlet uses only the four roots.
  let shift : P →ₐ[K] P :=
    aeval ![X (0 : Fin 5), X 1, X 2, X 3, X 4 + C z]
  let unshift : P →ₐ[K] P :=
    aeval ![X (0 : Fin 5), X 1, X 2, X 3, X 4 - C z]
  let S : P →ₐ[K] B := killCompl survivingRoot_injective
  have hleft : unshift.comp shift = AlgHom.id K P := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [unshift, shift]
  have hcomp : S.comp shift = boundaryEval(z) := by
    rw [show S = aeval ![X (0 : Fin 2), 0, X 1, 0, 0] from killCompl_survivingRoot]
    apply algHom_ext
    intro i
    fin_cases i <;> simp [shift]
  have hshift : shift (H n) = H n := by
    rw [show shift (H n) = aeval
        (![X (0 : Fin 5), X 1, X 2, X 3, X 4 + C z] ∘ Fin.castSucc) (hsymm (Fin 4) K n)
        from aeval_rename _ _ _]
    have hvars : (![X (0 : Fin 5), X 1, X 2, X 3, X 4 + C z] ∘
        (Fin.castSucc : Fin 4 → Fin 5)) = X ∘ Fin.castSucc := by
      funext i
      fin_cases i <;> rfl
    rw [hvars, ← rename_eq_aeval]
  have hne : boundaryEval(z) (H n) ≠ 0 := by
    intro h
    have hval := boundary_axis z n 0
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  have hcoord (i : Fin 2) : IsRelPrime (boundaryEval(z) (H n)) (X i) := by
    apply ((X_prime (R := K) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr ?_).symm
    intro h
    let axis : Fin 2 → K := Pi.single i.rev 1
    have hz := map_dvd (aeval axis) h
    have hvar : aeval axis (X i : B) = 0 := by
      rw [aeval_X]
      fin_cases i <;> simp [axis]
    rw [hvar, show aeval axis (boundaryEval(z) (H n)) = 1 from boundary_axis z n i.rev,
      zero_dvd_iff] at hz
    exact one_ne_zero hz
  have hrel : IsRelPrime (boundaryEval(z) (H n)) (boundaryEval(z) g) := by
    rw [hg]
    exact ((isUnit_iff_ne_zero.mpr hc).map C).isRelPrime_right.mul_right
      ((hcoord 0).pow_right) |>.mul_right ((hcoord 1).pow_right)
  have hsplit : IsRelPrime (shift (H n)) (shift g) := by
    apply isRelPrime_of_killCompl survivingRoot_injective (w := 1) (by simp)
    · rw [hshift]
      exact (hsymm_homogeneous n).rename_isHomogeneous
    · exact (congrArg (fun k : P →ₐ[K] B => k (H n)) hcomp).symm ▸ hne
    · simpa only [← hcomp, AlgHom.comp_apply] using hrel
  intro d hd hdg
  have hu := (hsplit (map_dvd shift hd) (map_dvd shift hdg)).map unshift
  simpa only [← AlgHom.comp_apply, hleft, AlgHom.id_apply] using hu

/-- The outer determinant supplies a nonzero generic outer block on the
complete homogeneous branch of the vertical divisor argument. -/
theorem hsymm_isRelPrime_outerDividedDet [CharZero K] (m : ℕ) (hm : 3 ≤ m) :
    IsRelPrime (H (m - 2)) (PeriodicMPSUniformVerticalSection.outerDividedDet (R := K) m) := by
  have hmcast : (m : K) + 2 ≠ 0 := by
    exact_mod_cast (show m + 2 ≠ 0 by omega)
  have hc : (-8 : K) * ((m : K) + 2) ^ 2 * 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hmcast)) (by norm_num)
  apply hsymm_isRelPrime_of_boundary_monomial (m - 2) _ 2 _ hc (3 * m + 4) (3 * m + 4)
  rw [show C (2 : K) = (2 : B) by exact map_ofNat C 2,
    PeriodicMPSUniformVerticalSection.outerDividedDet_boundary _ hm]
  simp only [show (2 : B) - 1 = 1 by norm_num, one_pow, mul_one, mul_pow]
  simp only [map_mul, map_neg, map_ofNat, map_pow, map_add, map_natCast]
  ring

end Boundary

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformVerticalBoundaryCoprime
