/- GID: D5/S3/VertexAlgebra/SourceMobius/OriginalCarrier
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/OriginalCarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer-unimodular original Carrier finite positive Sugawara flow. -/
import D5.S3.VertexAlgebra.SourceMobius.Coordinates
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

theorem gram_det_unit (D : LatticeData) (hu : IsUnit D.G.det) :
    IsUnit (gramComplex D).det := by
  have h := hu.map (Int.castRingHom ℂ)
  rw [RingHom.map_det] at h
  exact h

/-- The closed binomial source-coordinate substitution, charge by charge on
the original finite direct sum. Its identification with the constructed
algebra flow below consumes the proved coordinate formula. -/
def sourceFlow (D : LatticeData) (u : ℂ) : Module.End ℂ (Carrier D) :=
  Finsupp.lsum ℂ (fun a => (Finsupp.lsingle a).comp
    (aeval (fun x : Index D =>
      (∑ s ∈ Finset.range (x.2+1),
        (((x.2+1).choose (s+1) : ℂ) * u ^ (x.2-s)) • X (x.1,s)) +
        (u ^ (x.2+1)) • C (bilinear D (unitCharge D x.1) a : ℂ))).toLinearMap)

private theorem sourceFlow_single (D : LatticeData) (u : ℂ) (a : Charge D)
    (p : Oscillator D) :
    sourceFlow D u (Finsupp.single a p) = Finsupp.single a (sectorFlow D a u p) := by
  rw [sectorFlow_eq_aeval]
  simp [sourceFlow]

/-- The sharp original-source monomial bound with the actual inverse Gram
matrix obtained from the original integer determinant-unit hypothesis. -/
theorem actual_sugawara_one_monomial_bound (D : LatticeData) (hu : IsUnit D.G.det)
    (a : Charge D) (m : Index D →₀ ℕ) (c : ℂ) :
    (sugawaraMode D (gramComplex D)⁻¹ 1 ^ (m.weight (sourceWeight D) + 1))
      (Finsupp.single a (monomial m c)) = 0 := by
  rw [sugawara_pow_single D _ (Matrix.nonsing_inv_mul _ (gram_det_unit D hu))
    (Matrix.mul_nonsing_inv _ (gram_det_unit D hu)), sectorL1_monomial_bound, Finsupp.single_zero]

/-- Every original source admits a finite factorial flow of the existing
Sugawara mode. The actual cutoff is the maximum oscillator weighted degree
over its true finite charge support, independent of signed charge norm. -/
theorem actual_sourceFlow_eq_sum (D : LatticeData) (hu : IsUnit D.G.det)
    (u : ℂ) (v : Carrier D) :
    sourceFlow D u v =
      ∑ n ∈ Finset.range (v.support.sup
        (fun a => weightedTotalDegree (sourceWeight D) (v a)) + 1),
        (u ^ n / (n.factorial : ℂ)) • (sugawaraMode D (gramComplex D)⁻¹ 1 ^ n) v := by
  classical
  let R := v.support.sup (fun a => weightedTotalDegree (sourceWeight D) (v a))
  have hHG := Matrix.nonsing_inv_mul _ (gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (gram_det_unit D hu)
  have singles : (∑ a ∈ v.support, Finsupp.single a (v a)) = v := Finsupp.sum_single v
  have hsingle (a : Charge D) (ha : a ∈ v.support) :
      sourceFlow D u (Finsupp.single a (v a)) =
        ∑ n ∈ Finset.range (R+1), (u ^ n / (n.factorial : ℂ)) •
          (sugawaraMode D (gramComplex D)⁻¹ 1 ^ n) (Finsupp.single a (v a)) := by
    rw [sourceFlow_single, sectorFlow_eq_sum_of_bound D a u (v a) R (Finset.le_sup (f := fun a => weightedTotalDegree (sourceWeight D) (v a)) ha)]
    simp only [Finsupp.single_finsetSum, ← Finsupp.smul_single, sugawara_pow_single D _ hHG hGH]
  calc
    sourceFlow D u v = ∑ a ∈ v.support, sourceFlow D u (Finsupp.single a (v a)) := by
      rw [← map_sum, singles]
    _ = ∑ a ∈ v.support, ∑ n ∈ Finset.range (R+1),
        (u ^ n / (n.factorial : ℂ)) •
          (sugawaraMode D (gramComplex D)⁻¹ 1 ^ n) (Finsupp.single a (v a)) := by
      apply Finset.sum_congr rfl
      exact hsingle
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.smul_sum, ← map_sum, singles]

/-- Local nilpotence on the original Carrier at the same finite support bound. -/
theorem actual_sugawara_one_bound (D : LatticeData) (hu : IsUnit D.G.det) (v : Carrier D) :
    (sugawaraMode D (gramComplex D)⁻¹ 1 ^ (v.support.sup
      (fun a => weightedTotalDegree (sourceWeight D) (v a)) + 1)) v = 0 := by
  classical
  let R := v.support.sup (fun a => weightedTotalDegree (sourceWeight D) (v a))
  have singles : (∑ a ∈ v.support, Finsupp.single a (v a)) = v := Finsupp.sum_single v
  change (sugawaraMode D (gramComplex D)⁻¹ 1 ^ (R+1)) v = 0
  rw [← singles, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  let p := v a
  change (sugawaraMode D (gramComplex D)⁻¹ 1 ^ (R+1)) (Finsupp.single a p) = 0
  rw [p.as_sum, Finsupp.single_finsetSum, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have hl : m.weight (sourceWeight D) ≤ R :=
    (le_weightedTotalDegree (sourceWeight D) hm).trans
      (Finset.le_sup (f := fun a => weightedTotalDegree (sourceWeight D) (v a)) ha)
  have killed := actual_sugawara_one_monomial_bound D hu a m (p.coeff m)
  rw [show R+1 = (R - m.weight (sourceWeight D)) +
      (m.weight (sourceWeight D) + 1) by omega,
    pow_add, Module.End.mul_apply, killed, map_zero]


/-- Additive parameter composition on the full original finite direct sum. -/
theorem sourceFlow_add (D : LatticeData) (u v : ℂ) :
    sourceFlow D (u+v) = sourceFlow D u * sourceFlow D v := by
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext
  intro p
  change sourceFlow D (u+v) (Finsupp.single a p) =
    sourceFlow D u (sourceFlow D v (Finsupp.single a p))
  rw [sourceFlow_single, sourceFlow_single, sourceFlow_single, sectorFlow_add]

end D5.S3.VertexAlgebra.SourceMobius
