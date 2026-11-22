/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralRadicalAlgebra
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralRadicalAlgebra
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: The finite free chart of the trace-aligned mixed-transfer coefficients. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry.PeriodicMPSUniformSpectralCoefficients
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The finite free chart of the trace-aligned mixed-transfer coefficients

For the coefficients of `X⁴ - X³ + a X² - b X + c`, this presents the
determinant coordinates of the trace-aligned transfer on the chart where
`U`, `k` and `2` are units. The coefficient formulas are those of
`PeriodicMPSUniformTransferSpectrum.braFirst_charpoly_trace_aligned` and its
ket-first counterpart.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpectralRadicalAlgebra

open Polynomial

universe u v w

/-- The coefficients and units of the determinant chart. -/
structure Parameters (R : Type u) [CommRing R] where
  a : R
  b : R
  c : R
  U : Rˣ
  k : Rˣ
  two : Rˣ
  two_val : (two : R) = 2

namespace Parameters

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- Specialization along any ring homomorphism, including to a residue field. -/
def map (p : Parameters R) (f : R →+* S) : Parameters S where
  a := f p.a
  b := f p.b
  c := f p.c
  U := Units.map f p.U
  k := Units.map f p.k
  two := Units.map f p.two
  two_val := by change f (p.two : R) = 2; rw [p.two_val, map_ofNat]

/-- The sum of the two first determinants. -/
def sumD (p : Parameters R) : R := p.a + 4 * ↑p.U - 2 * p.b + (p.k : R) ^ 2

/-- The sum of the two scaled second determinants,
`(c - b²)/k² - 2U + b`, with division given by the unit inverse. -/
def sumS (p : Parameters R) : R :=
  (p.c - p.b ^ 2) * (↑p.k⁻¹ : R) ^ 2 - 2 * ↑p.U + p.b

/-- The discriminant of the difference of the first determinants. -/
def deltaD (p : Parameters R) : R := p.sumD ^ 2 - 4 * ↑p.U

/-- The discriminant of the difference of the scaled second determinants. -/
def deltaS (p : Parameters R) : R := p.sumS ^ 2 - 4 * (↑p.U * (↑p.U - p.b))

@[simp] theorem sumD_map (p : Parameters R) (f : R →+* S) :
    (p.map f).sumD = f p.sumD := by simp [sumD, map, map_ofNat]

@[simp] theorem sumS_map (p : Parameters R) (f : R →+* S) :
    (p.map f).sumS = f p.sumS := by simp [sumS, map, map_ofNat]

@[simp] theorem deltaD_map (p : Parameters R) (f : R →+* S) :
    (p.map f).deltaD = f p.deltaD := by simp only [deltaD, sumD_map, map_sub, map_pow, map_mul, map_ofNat]; rfl

@[simp] theorem deltaS_map (p : Parameters R) (f : R →+* S) :
    (p.map f).deltaS = f p.deltaS := by simp only [deltaS, sumS_map, map_sub, map_pow, map_mul, map_ofNat]; rfl

private theorem two_mul_half (p : Parameters R) : 2 * (↑p.two⁻¹ : R) = 1 := by
  rw [← p.two_val, Units.mul_inv]

private theorem k_sq_mul_inv_sq (p : Parameters R) :
    (p.k : R) ^ 2 * (↑p.k⁻¹ : R) ^ 2 = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

end Parameters

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

/-- The literal coefficient equations in the four split determinant coordinates. -/
@[ext] structure CoordinateFiber (p : Parameters R) where
  d : R
  db : R
  e : R
  eb : R
  prod_eq : d * db = ↑p.U
  coeff_a : d + db - 2 * (↑p.U + e * eb) - (p.k : R) ^ 2 = p.a
  coeff_b : ↑p.U - e * eb = p.b
  coeff_c : p.b ^ 2 + (p.k : R) ^ 2 * (d + eb) * (db + e) = p.c

/-- The square equations, allowing either radical to vanish. -/
@[ext] structure RadicalFiber (p : Parameters R) where
  x : R
  y : R
  x_sq : x ^ 2 = p.deltaD
  y_sq : y ^ 2 = p.deltaS

variable {p : Parameters R}

private theorem CoordinateFiber.sum_d (q : CoordinateFiber p) : q.d + q.db = p.sumD := by
  unfold Parameters.sumD
  linear_combination q.coeff_a - 2 * q.coeff_b

private theorem CoordinateFiber.sum_scaled_e (q : CoordinateFiber p) :
    q.d * q.e + q.db * q.eb = p.sumS := by
  have hcross : (q.d + q.eb) * (q.db + q.e) =
      (p.c - p.b ^ 2) * (↑p.k⁻¹ : R) ^ 2 := by
    calc
      _ = ((p.k : R) ^ 2 * (q.d + q.eb) * (q.db + q.e)) * (↑p.k⁻¹ : R) ^ 2 := by
        linear_combination -(q.d + q.eb) * (q.db + q.e) * p.k_sq_mul_inv_sq
      _ = _ := by linear_combination (↑p.k⁻¹ : R) ^ 2 * q.coeff_c
  unfold Parameters.sumS
  rw [← hcross]
  linear_combination -q.prod_eq + q.coeff_b

/-- Take the differences of the first determinants and of the scaled second determinants. -/
def CoordinateFiber.toRadical (q : CoordinateFiber p) : RadicalFiber p where
  x := q.d - q.db
  y := q.d * q.e - q.db * q.eb
  x_sq := by
    rw [Parameters.deltaD, ← q.sum_d]
    linear_combination -4 * q.prod_eq
  y_sq := by
    rw [Parameters.deltaS, ← q.sum_scaled_e]
    linear_combination (-4 * (q.e * q.eb)) * q.prod_eq + 4 * (p.U : R) * q.coeff_b

private theorem half_pair (p : Parameters R) (s t v : R) (ht : t ^ 2 = s ^ 2 - 4 * v) :
    let h : R := ↑p.two⁻¹
    (s + t) * h + (s - t) * h = s ∧
      (s + t) * h - (s - t) * h = t ∧
      ((s + t) * h) * ((s - t) * h) = v := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · linear_combination s * p.two_mul_half
  · linear_combination t * p.two_mul_half
  · linear_combination -(↑p.two⁻¹ : R) ^ 2 * ht +
      v * (2 * (↑p.two⁻¹ : R) + 1) * p.two_mul_half

/-- Reconstruct the determinant coordinates by halving the signed sums and
dividing the scaled second determinants by the corresponding first determinants. -/
def RadicalFiber.toCoordinates (r : RadicalFiber p) : CoordinateFiber p := by
  let d := (p.sumD + r.x) * (↑p.two⁻¹ : R)
  let db := (p.sumD - r.x) * (↑p.two⁻¹ : R)
  let s := (p.sumS + r.y) * (↑p.two⁻¹ : R)
  let sb := (p.sumS - r.y) * (↑p.two⁻¹ : R)
  let e := s * db * (↑p.U⁻¹ : R)
  let eb := sb * d * (↑p.U⁻¹ : R)
  obtain ⟨hdSum, _, hprod⟩ := half_pair p p.sumD r.x ↑p.U r.x_sq
  obtain ⟨hsSum, _, hsProd⟩ := half_pair p p.sumS r.y (↑p.U * (↑p.U - p.b)) r.y_sq
  change d + db = p.sumD at hdSum
  change d * db = ↑p.U at hprod
  change s + sb = p.sumS at hsSum
  change s * sb = ↑p.U * (↑p.U - p.b) at hsProd
  have hUinv : (p.U : R) * (↑p.U⁻¹ : R) = 1 := Units.mul_inv p.U
  have he : d * e = s := by
    dsimp only [e]
    linear_combination s * (↑p.U⁻¹ : R) * hprod + s * hUinv
  have heb : db * eb = sb := by
    dsimp only [eb]
    linear_combination sb * (↑p.U⁻¹ : R) * hprod + sb * hUinv
  have hV : e * eb = ↑p.U - p.b := by
    have hscaled : (p.U : R) * (e * eb) = (p.U : R) * (↑p.U - p.b) := by
      calc
        _ = (d * e) * (db * eb) := by
          rw [← hprod]
          ring
        _ = _ := by rw [he, heb, hsProd]
    linear_combination (↑p.U⁻¹ : R) * hscaled + (↑p.U - p.b - e * eb) * hUinv
  have hcross : (d + eb) * (db + e) =
      (p.c - p.b ^ 2) * (↑p.k⁻¹ : R) ^ 2 := by
    calc
      _ = d * db + e * eb + (d * e + db * eb) := by ring
      _ = _ := by rw [hprod, hV, he, heb, hsSum, Parameters.sumS]; ring
  refine ⟨d, db, e, eb, hprod, ?_, ?_, ?_⟩
  · rw [hdSum, hV, Parameters.sumD]
    ring
  · rw [hV]
    ring
  · linear_combination (p.k : R) ^ 2 * hcross + (p.c - p.b ^ 2) * p.k_sq_mul_inv_sq

@[simp] theorem CoordinateFiber.toRadical_toCoordinates (q : CoordinateFiber p) :
    q.toRadical.toCoordinates = q := by
  let q' := q.toRadical.toCoordinates
  have hd : q'.d = q.d := by
    change (p.sumD + (q.d - q.db)) * (↑p.two⁻¹ : R) = q.d
    rw [← q.sum_d]
    linear_combination q.d * p.two_mul_half
  have hdb : q'.db = q.db := by
    change (p.sumD - (q.d - q.db)) * (↑p.two⁻¹ : R) = q.db
    rw [← q.sum_d]
    linear_combination q.db * p.two_mul_half
  have hUinv : (p.U : R) * (↑p.U⁻¹ : R) = 1 := Units.mul_inv p.U
  change q' = q
  apply CoordinateFiber.ext hd hdb
  · change ((p.sumS + (q.d * q.e - q.db * q.eb)) * (↑p.two⁻¹ : R)) *
      q'.db * (↑p.U⁻¹ : R) = q.e
    rw [hdb, ← q.sum_scaled_e]
    linear_combination q.d * q.db * q.e * (↑p.U⁻¹ : R) * p.two_mul_half +
      q.e * (↑p.U⁻¹ : R) * q.prod_eq + q.e * hUinv
  · change ((p.sumS - (q.d * q.e - q.db * q.eb)) * (↑p.two⁻¹ : R)) *
      q'.d * (↑p.U⁻¹ : R) = q.eb
    rw [hd, ← q.sum_scaled_e]
    linear_combination q.d * q.db * q.eb * (↑p.U⁻¹ : R) * p.two_mul_half +
      q.eb * (↑p.U⁻¹ : R) * q.prod_eq + q.eb * hUinv

@[simp] theorem RadicalFiber.toCoordinates_toRadical (r : RadicalFiber p) :
    r.toCoordinates.toRadical = r := by
  let q := r.toCoordinates
  obtain ⟨_, hx, _⟩ := half_pair p p.sumD r.x ↑p.U r.x_sq
  obtain ⟨_, hy, _⟩ := half_pair p p.sumS r.y (↑p.U * (↑p.U - p.b)) r.y_sq
  have hUinv : (p.U : R) * (↑p.U⁻¹ : R) = 1 := Units.mul_inv p.U
  have he : q.d * q.e = (p.sumS + r.y) * (↑p.two⁻¹ : R) := by
    change q.d * (((p.sumS + r.y) * (↑p.two⁻¹ : R)) * q.db * (↑p.U⁻¹ : R)) = _
    linear_combination (p.sumS + r.y) * (↑p.two⁻¹ : R) *
      ((↑p.U⁻¹ : R) * q.prod_eq + hUinv)
  have heb : q.db * q.eb = (p.sumS - r.y) * (↑p.two⁻¹ : R) := by
    change q.db * (((p.sumS - r.y) * (↑p.two⁻¹ : R)) * q.d * (↑p.U⁻¹ : R)) = _
    linear_combination (p.sumS - r.y) * (↑p.two⁻¹ : R) *
      ((↑p.U⁻¹ : R) * q.prod_eq + hUinv)
  apply RadicalFiber.ext
  · exact hx
  · change q.d * q.e - q.db * q.eb = r.y
    rw [he, heb]
    exact hy

noncomputable section

section RadicalAlgebra

/-- The first monic polynomial of the radical presentation. -/
def polynomialD (p : Parameters R) : R[X] := X ^ 2 - C p.deltaD

/-- The first radical algebra. -/
abbrev FirstRadical (p : Parameters R) := AdjoinRoot (polynomialD p)

/-- The second monic polynomial, over the first radical algebra. -/
def polynomialS (p : Parameters R) : (FirstRadical p)[X] :=
  X ^ 2 - C (algebraMap R (FirstRadical p) p.deltaS)

/-- The iterated monic quadratic algebra of the chart. -/
abbrev RadicalAlgebra (p : Parameters R) := AdjoinRoot (polynomialS p)

/-- The difference of the two first determinants in the radical presentation. -/
def rootD (p : Parameters R) : RadicalAlgebra p :=
  algebraMap (FirstRadical p) (RadicalAlgebra p) (AdjoinRoot.root (polynomialD p))

/-- The difference of the two scaled second determinants in the radical presentation. -/
def rootS (p : Parameters R) : RadicalAlgebra p := AdjoinRoot.root (polynomialS p)

@[simp] theorem rootD_sq (p : Parameters R) :
    rootD p ^ 2 = algebraMap R (RadicalAlgebra p) p.deltaD := by
  have h : AdjoinRoot.mk (polynomialD p) (X ^ 2 - C p.deltaD) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  rw [rootD, ← map_pow, sub_eq_zero.mp h]
  rfl

@[simp] theorem rootS_sq (p : Parameters R) :
    rootS p ^ 2 = algebraMap R (RadicalAlgebra p) p.deltaS := by
  have h : AdjoinRoot.mk (polynomialS p)
      (X ^ 2 - C (algebraMap R (FirstRadical p) p.deltaS)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  exact sub_eq_zero.mp h

private theorem monicD (p : Parameters R) : (polynomialD p).Monic :=
  monic_X_pow_sub_C _ (by decide)

private theorem monicS (p : Parameters R) : (polynomialS p).Monic :=
  monic_X_pow_sub_C _ (by decide)

/-- The monic tower basis, indexed by the exponents of the two roots. -/
def radicalBasis (p : Parameters R) :
    Module.Basis (Fin 2 × Fin 2) R (RadicalAlgebra p) := by
  classical
  by_cases h : Nontrivial R
  · letI := h
    have hD : (polynomialD p).natDegree = 2 := natDegree_X_pow_sub_C
    letI : Nontrivial (FirstRadical p) :=
      (AdjoinRoot.of.injective_of_monic_of_degree_pos (monicD p)
        (by rw [Polynomial.degree_eq_natDegree (monicD p).ne_zero, hD]; decide)).nontrivial
    have hS : (polynomialS p).natDegree = 2 := natDegree_X_pow_sub_C
    exact (((AdjoinRoot.powerBasisAux' (monicD p)).reindex (finCongr hD)).smulTower
      ((AdjoinRoot.powerBasisAux' (monicS p)).reindex (finCongr hS)))
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    letI : Subsingleton (RadicalAlgebra p) := Module.subsingleton R (RadicalAlgebra p)
    exact Module.Basis.ofEquivFun (LinearEquiv.ofSubsingleton (RadicalAlgebra p) (Fin 2 × Fin 2 → R) :
      RadicalAlgebra p ≃ₗ[R] (Fin 2 × Fin 2 → R))

private theorem adjoinRoot_basis_apply {A : Type*} [CommRing A]
    {f : A[X]} (hf : f.Monic) (i : Fin f.natDegree) :
    AdjoinRoot.powerBasisAux' hf i = AdjoinRoot.root f ^ (i : ℕ) :=
  (AdjoinRoot.powerBasis' hf).basis_eq_pow i

@[simp] theorem radicalBasis_apply (p : Parameters R) (i j : Fin 2) :
    radicalBasis p (i, j) = rootD p ^ (i : ℕ) * rootS p ^ (j : ℕ) := by
  classical
  unfold radicalBasis
  split
  · simp [Module.Basis.smulTower_apply, adjoinRoot_basis_apply, Algebra.smul_def, rootD, rootS]
    rfl
  · rename_i h
    let fallback : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact @Subsingleton.elim _ (Module.subsingleton R (RadicalAlgebra p)) _ _

instance (p : Parameters R) : Module.Free R (RadicalAlgebra p) :=
  Module.Free.of_basis (radicalBasis p)

instance (p : Parameters R) : Module.Finite R (RadicalAlgebra p) :=
  Module.Finite.of_basis (radicalBasis p)

theorem radicalAlgebra_finrank [Nontrivial R] (p : Parameters R) :
    Module.finrank R (RadicalAlgebra p) = 4 := by
  rw [Module.finrank_eq_card_basis (radicalBasis p)]
  decide

/-- The two universal radicals. -/
def radicalPoint (p : Parameters R) :
    RadicalFiber (p.map (algebraMap R (RadicalAlgebra p))) :=
  ⟨rootD p, rootS p, by simp, by simp⟩

private def firstLift [Algebra R S] (r : RadicalFiber (p.map (algebraMap R S))) :
    FirstRadical p →ₐ[R] S :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) r.x
    (by simpa [polynomialD] using sub_eq_zero.mpr r.x_sq)

/-- Evaluate the radical algebra at a pair of roots in any base algebra. -/
def radicalLift [Algebra R S] (r : RadicalFiber (p.map (algebraMap R S))) :
    RadicalAlgebra p →ₐ[R] S :=
  AdjoinRoot.liftAlgHom _ (firstLift r) r.y
    (by
      simp only [polynomialS, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [AlgHom.coe_toRingHom, AlgHom.commutes, ← Parameters.deltaS_map, r.y_sq, sub_self])

@[simp] theorem radicalLift_rootD [Algebra R S]
    (r : RadicalFiber (p.map (algebraMap R S))) :
    radicalLift r (rootD p) = r.x := by
  simp [radicalLift, rootD, firstLift]

@[simp] theorem radicalLift_rootS [Algebra R S]
    (r : RadicalFiber (p.map (algebraMap R S))) :
    radicalLift r (rootS p) = r.y := by
  simp [radicalLift, rootS]

theorem radicalAlgHom_ext [Algebra R S] {f g : RadicalAlgebra p →ₐ[R] S}
    (hx : f (rootD p) = g (rootD p)) (hy : f (rootS p) = g (rootS p)) : f = g :=
  AdjoinRoot.algHom_ext' (AdjoinRoot.algHom_ext hx) hy

end RadicalAlgebra

section CoordinateAlgebra

open Determinant

private def relationProd (p : Parameters R) : MvPolynomial Determinant R :=
  MvPolynomial.X d * MvPolynomial.X db - MvPolynomial.C (p.U : R)

private def relationA (p : Parameters R) : MvPolynomial Determinant R :=
  let X := MvPolynomial.X
  let C := MvPolynomial.C
  X d + X db - 2 * (C (p.U : R) + X e * X eb) - C ((p.k : R) ^ 2) - C p.a

private def relationB (p : Parameters R) : MvPolynomial Determinant R :=
  MvPolynomial.C (p.U : R) - MvPolynomial.X e * MvPolynomial.X eb - MvPolynomial.C p.b

private def relationC (p : Parameters R) : MvPolynomial Determinant R :=
  let X := MvPolynomial.X
  let C := MvPolynomial.C
  C (p.b ^ 2) + C ((p.k : R) ^ 2) * (X d + X eb) * (X db + X e) - C p.c

/-- The ideal of the four original equations, with `d * db` fixed to `U`. -/
def coordinateIdeal (p : Parameters R) : Ideal (MvPolynomial Determinant R) :=
  Ideal.span {relationProd p, relationA p, relationB p, relationC p}

/-- The original four-coordinate quotient algebra of the same chart. -/
abbrev CoordinateAlgebra (p : Parameters R) := MvPolynomial Determinant R ⧸ coordinateIdeal p

/-- The image of a determinant variable in the coordinate quotient. -/
def coordinate (p : Parameters R) (i : Determinant) : CoordinateAlgebra p :=
  Ideal.Quotient.mk (coordinateIdeal p) (MvPolynomial.X i)

private theorem quotient_mk_C (p : Parameters R) (r : R) :
    Ideal.Quotient.mk (coordinateIdeal p) (MvPolynomial.C r) =
      algebraMap R (CoordinateAlgebra p) r := rfl

/-- The literal determinants in the coordinate quotient. -/
def coordinatePoint (p : Parameters R) :
    CoordinateFiber (p.map (algebraMap R (CoordinateAlgebra p))) := by
  have vanishes {g : MvPolynomial Determinant R}
      (hg : g ∈ ({relationProd p, relationA p, relationB p, relationC p} : Set _)) :
      Ideal.Quotient.mk (coordinateIdeal p) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hg)
  refine ⟨coordinate p d, coordinate p db, coordinate p e, coordinate p eb, ?_, ?_, ?_, ?_⟩
  · apply sub_eq_zero.mp
    have h := vanishes (g := relationProd p) (by simp)
    simp only [relationProd, map_sub, map_mul, quotient_mk_C] at h
    exact h
  · apply sub_eq_zero.mp
    have h := vanishes (g := relationA p) (by simp)
    simp only [relationA, map_sub, map_mul, map_add, map_ofNat, quotient_mk_C, map_pow] at h
    exact h
  · apply sub_eq_zero.mp
    have h := vanishes (g := relationB p) (by simp)
    simp only [relationB, map_sub, map_mul, quotient_mk_C] at h
    exact h
  · apply sub_eq_zero.mp
    have h := vanishes (g := relationC p) (by simp)
    simp only [relationC, map_sub, map_mul, map_add, quotient_mk_C, map_pow] at h
    exact h

/-- Evaluate the coordinate quotient at a solution of the four determinant equations. -/
def coordinateLift [Algebra R S] (q : CoordinateFiber (p.map (algebraMap R S))) :
    CoordinateAlgebra p →ₐ[R] S := by
  let eval := MvPolynomial.aeval (R := R) (fun i => match i with
    | d => q.d | db => q.db | e => q.e | eb => q.eb)
  refine Ideal.Quotient.liftₐ (coordinateIdeal p) eval ?_
  have hI : coordinateIdeal p ≤ RingHom.ker eval := by
    apply Ideal.span_le.mpr
    intro g hg
    change g ∈ RingHom.ker eval.toRingHom
    rw [RingHom.mem_ker]
    change eval g = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simpa [eval, relationProd, Parameters.map] using sub_eq_zero.mpr q.prod_eq
    · simpa [eval, relationA, Parameters.map, map_ofNat] using sub_eq_zero.mpr q.coeff_a
    · simpa [eval, relationB, Parameters.map] using sub_eq_zero.mpr q.coeff_b
    · simpa [eval, relationC, Parameters.map] using sub_eq_zero.mpr q.coeff_c
  exact fun g hg => RingHom.mem_ker.mp (hI hg)

@[simp] theorem coordinateLift_coordinate [Algebra R S]
    (q : CoordinateFiber (p.map (algebraMap R S))) (i : Determinant) :
    coordinateLift q (coordinate p i) = (match i with
      | d => q.d | db => q.db | e => q.e | eb => q.eb) := by
  change (Ideal.Quotient.liftₐ _ _ _) (Ideal.Quotient.mkₐ R _ (MvPolynomial.X i)) = _
  rw [← AlgHom.comp_apply, Ideal.Quotient.liftₐ_comp, MvPolynomial.aeval_X]

theorem coordinateAlgHom_ext [Algebra R S] {f g : CoordinateAlgebra p →ₐ[R] S}
    (h : ∀ i, f (coordinate p i) = g (coordinate p i)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  exact MvPolynomial.algHom_ext h

end CoordinateAlgebra

section Points

variable {T : Type w} [CommRing T] [Algebra R S] [Algebra R T]

/-- Push a solution of the literal equations along a homomorphism of base algebras. -/
def CoordinateFiber.postcompose (q : CoordinateFiber (p.map (algebraMap R S)))
    (f : S →ₐ[R] T) : CoordinateFiber (p.map (algebraMap R T)) where
  d := f q.d
  db := f q.db
  e := f q.e
  eb := f q.eb
  prod_eq := by simpa [Parameters.map] using congrArg f q.prod_eq
  coeff_a := by simpa [Parameters.map, map_ofNat] using congrArg f q.coeff_a
  coeff_b := by simpa [Parameters.map] using congrArg f q.coeff_b
  coeff_c := by simpa [Parameters.map] using congrArg f q.coeff_c

/-- Push a solution of the square equations along a homomorphism of base algebras. -/
def RadicalFiber.postcompose (r : RadicalFiber (p.map (algebraMap R S))) (f : S →ₐ[R] T) :
    RadicalFiber (p.map (algebraMap R T)) where
  x := f r.x
  y := f r.y
  x_sq := by simpa using congrArg f r.x_sq
  y_sq := by simpa using congrArg f r.y_sq

theorem CoordinateFiber.toRadical_postcompose
    (q : CoordinateFiber (p.map (algebraMap R S))) (f : S →ₐ[R] T) :
    (q.postcompose f).toRadical = q.toRadical.postcompose f := by
  apply RadicalFiber.ext <;> simp [CoordinateFiber.toRadical, CoordinateFiber.postcompose,
    RadicalFiber.postcompose]

theorem RadicalFiber.toCoordinates_postcompose
    (r : RadicalFiber (p.map (algebraMap R S))) (f : S →ₐ[R] T) :
    (r.postcompose f).toCoordinates = r.toCoordinates.postcompose f := by
  apply CoordinateFiber.ext <;>
    simp [RadicalFiber.toCoordinates, CoordinateFiber.postcompose, RadicalFiber.postcompose,
      Parameters.sumD, Parameters.sumS, Parameters.map, map_ofNat]

@[simp] theorem coordinatePoint_postcompose_lift
    (q : CoordinateFiber (p.map (algebraMap R S))) :
    (coordinatePoint p).postcompose (coordinateLift q) = q := by
  apply CoordinateFiber.ext
  · exact coordinateLift_coordinate q .d
  · exact coordinateLift_coordinate q .db
  · exact coordinateLift_coordinate q .e
  · exact coordinateLift_coordinate q .eb

@[simp] theorem radicalPoint_postcompose_lift (r : RadicalFiber (p.map (algebraMap R S))) :
    (radicalPoint p).postcompose (radicalLift r) = r := by
  apply RadicalFiber.ext
  · exact radicalLift_rootD r
  · exact radicalLift_rootS r

/-- Evaluation at the reconstructed determinants and at the two differences
gives inverse maps of the two quotient algebras over the guarded base. -/
def coordinateEquivRadicalAlgebra (p : Parameters R) :
    CoordinateAlgebra p ≃ₐ[R] RadicalAlgebra p := by
  let f := coordinateLift (radicalPoint p).toCoordinates
  let g := radicalLift (coordinatePoint p).toRadical
  have hfg : (coordinatePoint p).toRadical.postcompose f = radicalPoint p := by
    rw [← CoordinateFiber.toRadical_postcompose]
    simp [f]
  have hgf : (radicalPoint p).toCoordinates.postcompose g = coordinatePoint p := by
    rw [← RadicalFiber.toCoordinates_postcompose]
    simp [g]
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply radicalAlgHom_ext
    · simpa [g, RadicalFiber.postcompose, radicalPoint] using congrArg RadicalFiber.x hfg
    · simpa [g, RadicalFiber.postcompose, radicalPoint] using congrArg RadicalFiber.y hfg
  · apply coordinateAlgHom_ext
    intro i
    cases i
    · simpa [f, CoordinateFiber.postcompose, coordinatePoint] using congrArg CoordinateFiber.d hgf
    · simpa [f, CoordinateFiber.postcompose, coordinatePoint] using congrArg CoordinateFiber.db hgf
    · simpa [f, CoordinateFiber.postcompose, coordinatePoint] using congrArg CoordinateFiber.e hgf
    · simpa [f, CoordinateFiber.postcompose, coordinatePoint] using congrArg CoordinateFiber.eb hgf

@[simp] theorem coordinateEquivRadicalAlgebra_apply (p : Parameters R) (i : Determinant) :
    coordinateEquivRadicalAlgebra p (coordinate p i) = (match i with
      | .d => (radicalPoint p).toCoordinates.d
      | .db => (radicalPoint p).toCoordinates.db
      | .e => (radicalPoint p).toCoordinates.e
      | .eb => (radicalPoint p).toCoordinates.eb) :=
  coordinateLift_coordinate (radicalPoint p).toCoordinates i

@[simp] theorem coordinateEquivRadicalAlgebra_symm_rootD (p : Parameters R) :
    (coordinateEquivRadicalAlgebra p).symm (rootD p) = coordinate p .d - coordinate p .db :=
  radicalLift_rootD (coordinatePoint p).toRadical

@[simp] theorem coordinateEquivRadicalAlgebra_symm_rootS (p : Parameters R) :
    (coordinateEquivRadicalAlgebra p).symm (rootS p) =
      coordinate p .d * coordinate p .e - coordinate p .db * coordinate p .eb :=
  radicalLift_rootS (coordinatePoint p).toRadical

/-- The same four-element basis transported to the literal coordinate quotient. -/
def coordinateBasis (p : Parameters R) :
    Module.Basis (Fin 2 × Fin 2) R (CoordinateAlgebra p) :=
  (radicalBasis p).map (coordinateEquivRadicalAlgebra p).symm.toLinearEquiv

theorem coordinateAlgebra_finrank [Nontrivial R] (p : Parameters R) :
    Module.finrank R (CoordinateAlgebra p) = 4 := by
  rw [Module.finrank_eq_card_basis (coordinateBasis p)]
  decide

/-- Representability of the radical equations on points over any base algebra. -/
def radicalPointsEquiv (p : Parameters R) (S : Type v) [CommRing S] [Algebra R S] :
    (RadicalAlgebra p →ₐ[R] S) ≃ RadicalFiber (p.map (algebraMap R S)) where
  toFun f := (radicalPoint p).postcompose f
  invFun := radicalLift
  left_inv f := by
    apply radicalAlgHom_ext
    · exact radicalLift_rootD _
    · exact radicalLift_rootS _
  right_inv := radicalPoint_postcompose_lift

/-- The same universal property expressed using the original determinant equations. -/
def coordinatePointsEquiv (p : Parameters R) (S : Type v) [CommRing S] [Algebra R S] :
    (CoordinateAlgebra p →ₐ[R] S) ≃ CoordinateFiber (p.map (algebraMap R S)) where
  toFun f := (coordinatePoint p).postcompose f
  invFun := coordinateLift
  left_inv f := by
    apply coordinateAlgHom_ext
    intro i
    cases i <;> apply coordinateLift_coordinate
  right_inv := coordinatePoint_postcompose_lift

theorem radicalPointsEquiv_natural (f : RadicalAlgebra p →ₐ[R] S) (g : S →ₐ[R] T) :
    radicalPointsEquiv p T (g.comp f) = (radicalPointsEquiv p S f).postcompose g := by
  apply RadicalFiber.ext <;> rfl

theorem coordinatePointsEquiv_natural (f : CoordinateAlgebra p →ₐ[R] S) (g : S →ₐ[R] T) :
    coordinatePointsEquiv p T (g.comp f) = (coordinatePointsEquiv p S f).postcompose g := by
  apply CoordinateFiber.ext <;> rfl

end Points

section BaseChange

open scoped TensorProduct
open Algebra.TensorProduct

variable (p) (S) [Algebra R S]

private def liftToSpecialization :
    RadicalAlgebra p →ₐ[R] RadicalAlgebra (p.map (algebraMap R S)) := by
  let q := p.map (algebraMap R S)
  refine radicalLift (p := p) ⟨rootD q, rootS q, ?_, ?_⟩
  · rw [rootD_sq, Parameters.deltaD_map, Parameters.deltaD_map]
    exact (IsScalarTower.algebraMap_apply R S _ _).symm
  · rw [rootS_sq, Parameters.deltaS_map, Parameters.deltaS_map]
    exact (IsScalarTower.algebraMap_apply R S _ _).symm

private def liftFromSpecialization :
    RadicalAlgebra (p.map (algebraMap R S)) →ₐ[S] S ⊗[R] RadicalAlgebra p := by
  let i : RadicalAlgebra p →ₐ[R] S ⊗[R] RadicalAlgebra p := includeRight
  refine radicalLift (p := p.map (algebraMap R S)) ⟨i (rootD p), i (rootS p), ?_, ?_⟩
  · rw [← map_pow, rootD_sq, i.commutes, Parameters.deltaD_map, Parameters.deltaD_map]
    exact IsScalarTower.algebraMap_apply R S _ _
  · rw [← map_pow, rootS_sq, i.commutes, Parameters.deltaS_map, Parameters.deltaS_map]
    exact IsScalarTower.algebraMap_apply R S _ _

set_option maxHeartbeats 800000 in
/-- Base change to any commutative base algebra gives the same tower with
the specialized discriminants. In particular this computes every residue-field fiber. -/
def radicalBaseChange :
    S ⊗[R] RadicalAlgebra p ≃ₐ[S] RadicalAlgebra (p.map (algebraMap R S)) := by
  let q := p.map (algebraMap R S)
  let f : S ⊗[R] RadicalAlgebra p →ₐ[S] RadicalAlgebra q :=
    Algebra.TensorProduct.lift (Algebra.ofId S _) (liftToSpecialization (p := p) S)
      (fun _ _ => Commute.all _ _)
  let g := liftFromSpecialization (p := p) S
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply radicalAlgHom_ext
    · simp [f, g, liftFromSpecialization, liftToSpecialization]
    · simp [f, g, liftFromSpecialization, liftToSpecialization]
  · apply Algebra.TensorProduct.ext
    · exact AlgHom.ext (fun s => by simpa using (g.comp f).commutes s)
    · apply radicalAlgHom_ext
      · simp [f, g, liftFromSpecialization, liftToSpecialization]
      · simp [f, g, liftFromSpecialization, liftToSpecialization]

@[simp] theorem radicalBaseChange_rootD :
    radicalBaseChange (p := p) S (1 ⊗ₜ[R] rootD p) = rootD (p.map (algebraMap R S)) := by
  simp [radicalBaseChange, liftToSpecialization]

@[simp] theorem radicalBaseChange_rootS :
    radicalBaseChange (p := p) S (1 ⊗ₜ[R] rootS p) = rootS (p.map (algebraMap R S)) := by
  simp [radicalBaseChange, liftToSpecialization]

end BaseChange

section Divisors

local instance (p : Parameters R) : Algebra.IsIntegral R (RadicalAlgebra p) :=
  Algebra.IsIntegral.of_finite R _

/-- Integral incomparability and flat going-down give equality of heights
for every prime and its contraction. -/
theorem height_under (P : Ideal (RadicalAlgebra p)) [P.IsPrime] :
    (P.under R).height = P.height := by
  let A := RadicalAlgebra p
  let Pspec : PrimeSpectrum A := ⟨P, inferInstance⟩
  let pSpec := PrimeSpectrum.comap (algebraMap R A) Pspec
  have : P.LiesOver pSpec.asIdeal := ⟨rfl⟩
  change pSpec.asIdeal.height = Pspec.asIdeal.height
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  apply le_antisymm
  · apply Order.height_le_iff'.mpr
    intro chain hlast
    have : P.LiesOver chain.last.asIdeal := hlast ▸ inferInstance
    obtain ⟨lifted, hlen, hlast', _⟩ := P.exists_ltSeries_of_hasGoingDown chain
    rw [← hlen]
    exact Order.length_le_height (le_of_eq hlast')
  · apply Order.height_le_iff'.mpr
    intro chain hlast
    have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
      intro Q Q' h
      have : Q.asIdeal.IsPrime := Q.isPrime
      exact Ideal.IsIntegral.under_lt_under (R := R)
        (show Q.asIdeal < Q'.asIdeal from h)
    let contracted := chain.map (PrimeSpectrum.comap (algebraMap R A)) hstrict
    have hlast' : contracted.last = pSpec := by
      simp [contracted, hlast, pSpec]
    have hlen : contracted.length = chain.length := rfl
    rw [← hlen]
    exact Order.length_le_height (le_of_eq hlast')

/-- The scalar obtained by pairing a linear form in the two radicals with
its conjugate under the second sign change. -/
def linearContraction (p : Parameters R) (α β : R) : R :=
  p.deltaD * α ^ 2 - p.deltaS * β ^ 2

/-- A linear form and its conjugate under the second sign change multiply
to the scalar that must vanish on the contracted ideal. -/
theorem linearForm_mul_conjugate (p : Parameters R) (α β : R) :
    let a := algebraMap R (RadicalAlgebra p) α * rootD p
    let b := algebraMap R (RadicalAlgebra p) β * rootS p
    (a + b) * (a - b) = algebraMap R (RadicalAlgebra p) (linearContraction p α β) := by
  dsimp only
  calc
    _ = (algebraMap R (RadicalAlgebra p) α) ^ 2 * rootD p ^ 2 -
        (algebraMap R (RadicalAlgebra p) β) ^ 2 * rootS p ^ 2 := by ring
    _ = _ := by simp [linearContraction, mul_comm]

theorem linearContraction_mem_under (P : Ideal (RadicalAlgebra p)) {α β : R}
    (h : algebraMap R (RadicalAlgebra p) α * rootD p +
      algebraMap R (RadicalAlgebra p) β * rootS p ∈ P) :
    linearContraction p α β ∈ P.under R := by
  change algebraMap R (RadicalAlgebra p) (linearContraction p α β) ∈ P
  rw [← linearForm_mul_conjugate]
  exact P.mul_mem_right _ h

/-- If a height-one prime contains the two selected linear forms, there is
a height-one prime of the base containing both scalar contractions. -/
theorem contract_critical_pair (P : Ideal (RadicalAlgebra p)) [P.IsPrime] (hP : P.height = 1)
    (α₀ β₀ α₉ β₉ : R)
    (h₀ : algebraMap R (RadicalAlgebra p) α₀ * rootD p +
      algebraMap R (RadicalAlgebra p) β₀ * rootS p ∈ P)
    (h₉ : algebraMap R (RadicalAlgebra p) α₉ * rootD p +
      algebraMap R (RadicalAlgebra p) β₉ * rootS p ∈ P) :
    (P.under R).IsPrime ∧ (P.under R).height = 1 ∧
      linearContraction p α₀ β₀ ∈ P.under R ∧ linearContraction p α₉ β₉ ∈ P.under R :=
  ⟨Ideal.IsPrime.under R P, (height_under P).trans hP,
    linearContraction_mem_under P h₀, linearContraction_mem_under P h₉⟩

end Divisors

end

private noncomputable def adjoinSquareEquiv {R : Type*} [CommRing R] (r : R) :
    AdjoinRoot (X ^ 2 - C r) ≃ₐ[R] QuadraticAlgebra R r 0 := by
  let f := (X ^ 2 - C r : R[X])
  let forward : AdjoinRoot f →ₐ[R] QuadraticAlgebra R r 0 :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) QuadraticAlgebra.omega (by
      simp [f, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap])
  have hroot : AdjoinRoot.root f ^ 2 = algebraMap R (AdjoinRoot f) r := by
    have h : AdjoinRoot.mk f (X ^ 2 - C r) = 0 := AdjoinRoot.mk_self
    simpa [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] using h
  let backward : QuadraticAlgebra R r 0 →ₐ[R] AdjoinRoot f :=
    QuadraticAlgebra.lift ⟨AdjoinRoot.root f, by
      simpa [Algebra.smul_def, ← pow_two] using hroot⟩
  have hb : backward (QuadraticAlgebra.omega : QuadraticAlgebra R r 0) = AdjoinRoot.root f := by
    simp [backward, QuadraticAlgebra.lift_apply_apply]
  have hf : forward (AdjoinRoot.root f) = (QuadraticAlgebra.omega : QuadraticAlgebra R r 0) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply QuadraticAlgebra.algHom_ext
    change forward (backward QuadraticAlgebra.omega) = QuadraticAlgebra.omega
    rw [hb, hf]
  · apply AdjoinRoot.algHom_ext
    change backward (forward (AdjoinRoot.root f)) = AdjoinRoot.root f
    rw [hf, hb]

private noncomputable def radicalTowerEquiv {F : Type*} [CommRing F]
    (p : Parameters F)
    (r s : F) (hr : p.deltaD = r) (hs : p.deltaS = s) :
    RadicalAlgebra p ≃+*
      QuadraticAlgebra (QuadraticAlgebra F r 0)
        (algebraMap F (QuadraticAlgebra F r 0) s) 0 := by
  subst r
  subst s
  let e : FirstRadical p ≃ₐ[F]
      QuadraticAlgebra F p.deltaD 0 := adjoinSquareEquiv p.deltaD
  let s := algebraMap F (QuadraticAlgebra F p.deltaD 0) p.deltaS
  let g := AdjoinRoot.mapRingEquiv e.toRingEquiv
    (polynomialS p) (X ^ 2 - C s) (by
      simp only [polynomialS, Polynomial.map_sub,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      change Associated (X ^ 2 - C (e (algebraMap F _ p.deltaS))) (X ^ 2 - C s)
      rw [e.commutes])
  exact g.trans (adjoinSquareEquiv s).toRingEquiv

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformSpectralRadicalAlgebra
