/- GID: D5/S3/ArithUnits/MinacNguyenTanQuestion35
   generality: G
   mirror-B: D5/B/S3/ArithUnits/MinacNguyenTanQuestion35
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Basic]
   utility: none
   digest: Exact sums of units with prescribed augmentation in finite group algebras. -/

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.Finsupp.Fintype
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Tactic

/-!
The standard augmentation descends through the Jacobson radical. In the
Wedderburn product its image selects a simple factor; injectivity identifies
that factor with the scalar field. Each other matrix factor admits two-unit
sums by rank normal form and a scalar distinct from zero and one. Padding these
sums preserves the original number of summands. Lifting quotient units and
adding the radical error to one summand preserves every augmentation.
-/

namespace D5.S3.ArithUnits.MinacNguyenTanQuestion35

/-- Exactly `n` summands, with repetitions allowed, from a specified subset. -/
def HasNSumProperty {R : Type*} [AddCommMonoid R] (S : Set R) (n : ℕ) : Prop :=
  ∀ r : R, ∃ a : Fin n → R, (∀ i, a i ∈ S) ∧ ∑ i, a i = r

/-- The standard group-algebra augmentation, sending every group basis vector to one. -/
noncomputable def augmentation (F G : Type*) [Field F] [Group G] :
    MonoidAlgebra F G →ₐ[F] F :=
  MonoidAlgebra.lift F F G (1 : G →* F)

/-- The genuine units whose standard augmentation belongs to `U`. -/
noncomputable def augmentationUnitSubgroup (F G : Type*) [Field F] [Group G]
    (U : Subgroup Fˣ) : Subgroup (MonoidAlgebra F G)ˣ :=
  U.comap (Units.map (augmentation F G).toRingHom.toMonoidHom)

/-- Mináč–Nguyen–Tân Question 3.5 with the original number of summands. -/
theorem result (F G : Type*) [Field F] [Group G] [Finite F] [Finite G]
    (U : Subgroup Fˣ) (hminus : (-1 : Fˣ) ∈ U)
    (n : ℕ) (hcard : 2 < Nat.card F) (hn : 2 ≤ n)
    (hF : HasNSumProperty (Units.val '' (U : Set Fˣ)) n) :
    HasNSumProperty (Units.val '' (augmentationUnitSubgroup F G U :
      Set (MonoidAlgebra F G)ˣ)) n := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype G := Fintype.ofFinite G
  let R := MonoidAlgebra F G
  letI : Fintype R := Fintype.ofEquiv (G →₀ F) MonoidAlgebra.coeffEquiv.symm
  letI : IsArtinianRing R := isArtinian_of_finite
  let J : Ideal R := Ring.jacobson R
  let Q := R ⧸ J
  let q : R →ₐ[F] Q := Ideal.Quotient.mkₐ F J
  let eps : R →ₐ[F] F := augmentation F G
  have hepssurj : Function.Surjective eps := by
    intro a
    refine ⟨MonoidAlgebra.single 1 a, ?_⟩
    change (MonoidAlgebra.lift F F G (1 : G →* F)) (MonoidAlgebra.single (1 : G) a) = a
    rw [MonoidAlgebra.lift_single]
    simp
  letI : RingHomSurjective eps.toRingHom := ⟨hepssurj⟩
  have hJ : ∀ x : R, x ∈ J → eps x = 0 := by
    intro x hx
    have h : eps x ∈ Ring.jacobson F := Ring.le_comap_jacobson eps.toRingHom hx
    rw [IsSemisimpleRing.jacobson_eq_bot F] at h
    exact h
  let epsQ : Q →ₐ[F] F := Ideal.Quotient.liftₐ J eps hJ
  have hepsQ : ∀ x, epsQ (q x) = eps x := fun _ => rfl
  have hLift : ∀ r : R, IsUnit (q r) → IsUnit r := by
    intro r hu
    obtain ⟨k, hk⟩ := IsSemiprimaryRing.isNilpotent (R := R)
    obtain ⟨v, hv⟩ := hu
    obtain ⟨s, hs⟩ := Ideal.Quotient.mkₐ_surjective F J (↑v⁻¹ : Q)
    have hprod : q (r * s) = 1 := by
      rw [map_mul, hs, ← hv]
      exact v.val_inv
    have hz : r * s - 1 ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (r * s - 1) = 0
      rw [map_sub, map_one, hprod, sub_self]
    have hnilst : IsNilpotent (r * s - 1) :=
      ⟨k, Ideal.pow_eq_zero_of_mem hk le_rfl hz⟩
    have hU : IsUnit (r * s) := by
      simpa only [sub_add_cancel] using hnilst.isUnit_add_one
    exact isUnit_of_mul_isUnit_left hU
  have hmatrix : ∀ (K : Type _) [Field K] (a : K), a ≠ 0 → a ≠ 1 →
      ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) K),
        ∃ A B : Matrix (Fin m) (Fin m) K, IsUnit A ∧ IsUnit B ∧ A + B = M := by
    intro K _ a ha haone m M
    obtain ⟨V, W, e, hV, hW, hnormal⟩ := Matrix.exists_rank_normal_form M
    let w : Fin m → K := fun i => Sum.elim (fun _ => 1) (fun _ => 0) (e i)
    have hdiag : (Matrix.fromBlocks 1 0 0 0).submatrix e e = Matrix.diagonal w := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
        Matrix.submatrix_diagonal_equiv]
      rfl
    have hC : IsUnit (Matrix.diagonal (fun _ : Fin m => a)) :=
      Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun _ => isUnit_iff_ne_zero.mpr ha)
    have hD : IsUnit (Matrix.diagonal (fun i => w i - a)) := by
      apply Matrix.isUnit_diagonal.mpr
      apply Pi.isUnit_iff.mpr
      intro i
      apply isUnit_iff_ne_zero.mpr
      dsimp [w]
      cases e i with
      | inl j => simpa [sub_ne_zero] using haone.symm
      | inr j => simpa using ha
    obtain ⟨v, hv⟩ := hV
    obtain ⟨z, hz⟩ := hW
    refine ⟨(↑(v⁻¹) : Matrix (Fin m) (Fin m) K) * Matrix.diagonal (fun _ => a) * (↑(z⁻¹) : Matrix (Fin m) (Fin m) K),
      (↑(v⁻¹) : Matrix (Fin m) (Fin m) K) * Matrix.diagonal (fun i => w i - a) * (↑(z⁻¹) : Matrix (Fin m) (Fin m) K),
      (v⁻¹).isUnit.mul hC |>.mul (z⁻¹).isUnit,
      (v⁻¹).isUnit.mul hD |>.mul (z⁻¹).isUnit, ?_⟩
    rw [← add_mul, ← mul_add, Matrix.diagonal_add]
    have hw : (fun i => a + (w i - a)) = w := by ext; ring
    rw [hw, ← hdiag, ← hnormal, ← hv, ← hz]
    simp [mul_assoc]
  have hmatrixN : ∀ (K : Type _) [Field K] (a : K), a ≠ 0 → a ≠ 1 →
      ∀ (m k : ℕ) (M : Matrix (Fin m) (Fin m) K),
        ∃ f : Fin (k + 2) → Matrix (Fin m) (Fin m) K,
          (∀ i, IsUnit (f i)) ∧ ∑ i, f i = M := by
    intro K _ a ha haone m k
    induction k with
    | zero =>
      intro M
      obtain ⟨A, B, hA, hB, hsum⟩ := hmatrix K a ha haone m M
      refine ⟨![A, B], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hA, hB]
      · simpa [Fin.sum_univ_two] using hsum
    | succ k ih =>
      intro M
      obtain ⟨f, hf, hsum⟩ := ih (M - 1)
      refine ⟨Fin.cons 1 f, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simpa using hf j
      · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
        abel
  haveI : IsSemisimpleRing Q := inferInstance
  obtain ⟨t, D, d, hdiv, halg, hmod, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite F Q
  letI := hdiv
  letI := halg
  letI := hmod
  letI := hd
  let P := Π i : Fin t, Matrix (Fin (d i)) (Fin (d i)) (D i)
  let phi : P →ₐ[F] F := epsQ.comp e.symm.toAlgHom
  have hidem (i : Fin t) : phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) = 0 ∨
      phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) = 1 := by
    let y := phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))
    have hy : y * y = y := by
      rw [← map_mul]
      apply congrArg phi
      change (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) : P) *
        Pi.single i 1 = Pi.single i 1
      apply funext
      intro j
      change ((Pi.single i 1 : P) j) * ((Pi.single i 1 : P) j) = (Pi.single i 1 : P) j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    have hz : y * (y - 1) = 0 := by rw [mul_sub, hy, mul_one, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hsumone : (∑ i : Fin t, phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)))) = 1 := by
    rw [← map_sum]
    have hsum : (∑ i : Fin t, (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) : P)) = 1 := by
      ext j
      simp
    rw [hsum, map_one]
  obtain ⟨i, hi⟩ : ∃ i : Fin t,
      phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) = 1 := by
    by_contra! h
    have hz : ∀ i : Fin t, phi (Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i))) = 0 :=
      fun i => (hidem i).resolve_right (h i)
    simp_rw [hz] at hsumone
    simpa using hsumone
  let fi : Matrix (Fin (d i)) (Fin (d i)) (D i) →+* F := {
    toFun := fun x => phi (Pi.single i x)
    map_zero' := by simp
    map_one' := hi
    map_add' := by
      intro x y
      rw [← map_add]
      apply congrArg phi
      change (Pi.single i (x + y) : P) = (Pi.single i x : P) + (Pi.single i y : P)
      apply funext
      intro j
      change (Pi.single i (x + y) : P) j = (Pi.single i x : P) j + (Pi.single i y : P) j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    map_mul' := by
      intro x y
      rw [← map_mul]
      apply congrArg phi
      change (Pi.single i (x * y) : P) = (Pi.single i x : P) * (Pi.single i y : P)
      apply funext
      intro j
      change (Pi.single i (x * y) : P) j = (Pi.single i x : P) j * (Pi.single i y : P) j
      by_cases h : j = i
      · subst j; simp
      · simp [h] }
  have hfactor (x : P) : phi x = fi (x i) := by
    have hsingle : Pi.single i (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) * x = Pi.single i (x i) := by
      apply funext
      intro j
      change (Pi.single i 1 : P) j * x j = (Pi.single i (x i) : P) j
      by_cases h : j = i
      · subst j; simp
      · simp [h]
    change phi x = phi (Pi.single i (x i))
    rw [← hsingle, map_mul, hi, one_mul]
  have hscalar (b : F) : fi (algebraMap F (Matrix (Fin (d i)) (Fin (d i)) (D i)) b) = b := by
    simpa [P, Pi.algebraMap_apply] using (hfactor (algebraMap F P b)).symm.trans (phi.commutes b)
  have hselected (x : P) : x i = algebraMap F (Matrix (Fin (d i)) (Fin (d i)) (D i)) (phi x) := by
    apply fi.injective
    rw [hscalar, ← hfactor]
  letI : ∀ j : Fin t, Finite (D j) := fun j => Module.finite_of_finite F
  have haF : ∃ b : F, b ≠ 0 ∧ b ≠ 1 := by
    by_contra! h
    have hbound : Fintype.card F ≤ 2 := by
      have hsubset : (Finset.univ : Finset F) ⊆ {0, 1} := by
        intro b _
        by_cases hb : b = 0
        · simp [hb]
        · simp [h b hb]
      calc
        Fintype.card F = (Finset.univ : Finset F).card := rfl
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsubset
        _ ≤ 2 := by simp
    rw [Nat.card_eq_fintype_card] at hcard
    exact (not_le_of_gt hcard) hbound
  obtain ⟨b, hbzero, hbone⟩ := haF
  intro r
  let x : P := e (q r)
  obtain ⟨a, ha, hasum⟩ := hF (phi x)
  have haUnit (l : Fin n) : IsUnit (a l) := by
    obtain ⟨u, hu, huv⟩ := ha l
    exact huv ▸ u.isUnit
  have hother (j : Fin t) : ∃ f : Fin n → Matrix (Fin (d j)) (Fin (d j)) (D j),
      (∀ l, IsUnit (f l)) ∧ ∑ l, f l = x j := by
    have hz : algebraMap F (D j) b ≠ 0 := by
      exact (map_ne_zero (algebraMap F (D j))).mpr hbzero
    have ho : algebraMap F (D j) b ≠ 1 := by
      intro h
      apply hbone
      exact (algebraMap F (D j)).injective (by simpa using h)
    have H := hmatrixN (D j) (algebraMap F (D j) b) hz ho (d j) (n - 2) (x j)
    have hlen : n - 2 + 2 = n := Nat.sub_add_cancel hn
    rw [hlen] at H
    exact H
  choose f hf hfsum using hother
  let y : Fin n → P := fun l j =>
    if j = i then algebraMap F (Matrix (Fin (d j)) (Fin (d j)) (D j)) (a l) else f j l
  have hyunit (l : Fin n) : IsUnit (y l) := by
    apply Pi.isUnit_iff.mpr
    intro j
    by_cases hj : j = i
    · simp only [y, hj, ite_true]
      exact (haUnit l).map (algebraMap F (Matrix (Fin (d j)) (Fin (d j)) (D j)))
    · simpa only [y, hj, ite_false] using hf j l
  have hysum : ∑ l, y l = x := by
    apply funext
    intro j
    rw [Finset.sum_apply]
    by_cases hj : j = i
    · subst j
      simp only [y, ite_true]
      rw [← map_sum, hasum, ← hselected]
    · simpa only [y, hj, ite_false] using hfsum j
  have hyaug (l : Fin n) : phi (y l) = a l := by
    rw [hfactor]
    simp only [y, ite_true]
    exact hscalar (a l)
  choose z hz using fun l : Fin n => Ideal.Quotient.mkₐ_surjective F J (e.symm (y l))
  have hqunit (l : Fin n) : IsUnit (q (z l)) := by
    rw [hz]
    exact (hyunit l).map e.symm.toRingHom
  have hsumq : q (∑ l, z l) = q r := by
    rw [map_sum]
    trans ∑ l, e.symm (y l)
    · apply Finset.sum_congr rfl
      intro l _
      exact hz l
    · rw [← map_sum, hysum]
      exact e.symm_apply_apply (q r)
  let delta : R := r - ∑ l, z l
  have hqdelta : q delta = 0 := by
    rw [map_sub, hsumq, sub_self]
  have hepsdelta : eps delta = 0 := hJ delta (Ideal.Quotient.eq_zero_iff_mem.mp hqdelta)
  letI : NeZero n := ⟨by omega⟩
  let w : Fin n → R := fun l => z l + if l = 0 then delta else 0
  have hqw (l : Fin n) : q (w l) = q (z l) := by
    by_cases h : l = 0 <;> simp [w, h, map_add, hqdelta]
  have hwunit (l : Fin n) : IsUnit (w l) :=
    hLift (w l) ((hqw l).symm ▸ hqunit l)
  have hwaug (l : Fin n) : eps (w l) = a l := by
    rw [← hepsQ, hqw, hz]
    change phi (y l) = a l
    exact hyaug l
  refine ⟨w, ?_, ?_⟩
  · intro l
    obtain ⟨v, hv⟩ := hwunit l
    obtain ⟨u, hu, huv⟩ := ha l
    refine ⟨v, ?_, hv⟩
    change Units.map (augmentation F G).toRingHom.toMonoidHom v ∈ U
    have heq : Units.map (augmentation F G).toRingHom.toMonoidHom v = u := by
      apply Units.ext
      change eps (↑v) = ↑u
      rw [hv, hwaug]
      exact huv.symm
    exact heq.symm ▸ hu
  · change (∑ l : Fin n, (z l + if l = 0 then delta else 0)) = r
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp [delta]
    abel



#print axioms result
#print axioms augmentation
#print axioms augmentationUnitSubgroup

end D5.S3.ArithUnits.MinacNguyenTanQuestion35
