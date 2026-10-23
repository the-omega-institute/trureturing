/- GID: D5/S3/VertexAlgebra/Sectors/LatticeNeutralVertexAlgebra
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeNeutralVertexAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The neutral sector is an actual vertex algebra acting on every charge sector. -/

import D5.S3.VertexAlgebra.Sectors.LatticeSectorBorcherds

/-!
The neutral Heisenberg vertex algebra is the charge-zero restriction of the
actual ordinary lattice vertex algebra. Its modules are the separately
labelled charge sectors, not modules for the full charged lattice algebra.
All ranks and degenerate forms are retained. Classical sources and the
finite-residue attribution are those of the actual field suppliers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorIntertwiner
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeSugawaraConformal
open LatticeActualVertexAlgebra FieldNormalProduct FieldNormalProductLocality
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- The state-field map on H_D=F_0, with the actual statewise pole bound. -/
def neutralY (D : LatticeData) : Sector D 0 →ₗ[ℂ] VertexOperator ℂ (Sector D 0) where
  toFun a := VertexOperator.of_coeff (fun k => action D 0 a (-k - 1)) (by
    intro v
    obtain ⟨N, hN⟩ := canonical_truncation D 0 0 a v
    refine ⟨-N, ?_⟩
    intro k hk
    by_contra low
    exact hk (hN (-k - 1) (by omega)))
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    simp [VertexOperator.coeff_eq_ncoeff, VertexOperator.ncoeff_of_coeff]
  map_smul' c a := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro v
    simp [VertexOperator.coeff_eq_ncoeff, VertexOperator.ncoeff_of_coeff]

@[simp] theorem neutralY_modes (D : LatticeData) (a : Sector D 0) (n : ℤ) :
    ((neutralY D a)[[n]]) = action D 0 a n := by
  simp only [neutralY, LinearMap.coe_mk, AddHom.coe_mk,
    VertexOperator.ncoeff_of_coeff, show -(-n - 1) - 1 = n by omega]

theorem action_vacuum (D : LatticeData) (δ : Charge D) (n : ℤ) :
    action D δ 1 n = if n = -1 then LinearMap.id else 0 := by
  apply LinearMap.ext
  intro v
  simp only [action, canonical, inclusion, projection, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.lapply_apply, zero_add]
  rw [stateField_ground, actual_zero, identity_modes]
  split_ifs <;> simp

private theorem neutral_creation (D : LatticeData) (a : Sector D 0) :
    ((neutralY D a)[[-1]]) 1 = a := by
  rw [neutralY_modes]
  have h := congrArg (fun v : Carrier D => v 0)
    (stateField_creation D (Finsupp.single 0 a))
  simpa [action, canonical, inclusion, projection, vacuum] using h

private theorem neutral_creativity (D : LatticeData) (a : Sector D 0)
    (n : ℤ) (hn : 0 ≤ n) : ((neutralY D a)[[n]]) 1 = 0 := by
  rw [neutralY_modes]
  have h := congrArg (fun v : Carrier D => v 0)
    (stateField_creativity D (Finsupp.single 0 a) n hn)
  simpa [action, canonical, inclusion, projection, vacuum] using h

private theorem neutral_locality (D : LatticeData) (a b : Sector D 0) :
    ∃ N : ℕ, delta^[N] (commutator (neutralY D a) (neutralY D b)) = 0 := by
  obtain ⟨N, hN⟩ := LatticeAllStateLocality.stateField_locality D
    (Finsupp.single 0 a) (Finsupp.single 0 b)
  have transfer (k : ℕ) (p q : ℤ) (v : Sector D 0) :
      Finsupp.single (0 : Charge D)
        ((delta^[k] (commutator (neutralY D a) (neutralY D b))) p q v) =
      (delta^[k] (commutator (Y D (Finsupp.single 0 a))
        (Y D (Finsupp.single 0 b)))) p q (Finsupp.single 0 v) := by
    induction k generalizing p q with
    | zero => simp [FieldNormalProductLocality.commutator, neutralY_modes, Module.End.mul_apply,
        LinearMap.sub_apply, Finsupp.single_sub, single_action]
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [delta, LinearMap.sub_apply, Finsupp.single_sub]
      rw [ih, ih]
  refine ⟨N, ?_⟩
  funext p q
  apply LinearMap.ext
  intro v
  have h := transfer N p q v
  rw [hN] at h
  have h' := congrArg (fun w : Carrier D => w 0) h
  simpa using h'

/-- Actual neutral vertex algebra; the charged sectors are not used as its algebra carrier. -/
def neutralVertexAlgebra (D : LatticeData) : StateFieldVertexAlgebra (Sector D 0) where
  stateField := neutralY D
  vacuum := 1
  translation := sectorT D 0
  vacuum_field := by
    apply HVertexOperator.coeff_inj
    funext k
    rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff,
      neutralY_modes, action_vacuum]
    rw [identityField, VertexOperator.ncoeff_of_coeff]
    split_ifs <;> first | rfl | omega
  creation := neutral_creation D
  creativity := neutral_creativity D
  translation_vacuum := by
    simp [sectorT, sectorTranslation, chargePolynomial]
  covariance a n := by
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f : Oscillator D →ₗ[ℂ] Oscillator D => f v)
      (canonical_target_derivative D 0 0 a n)
    simpa [neutralY_modes, action, sectorT, sectorTranslation, chargePolynomial,
      LinearMap.comp_apply, Module.End.mul_apply] using h
  locality := neutral_locality D
  borcherds a b c p q r := by
    have h := canonical_borcherds D 0 0 a b c p q r
    simp_rw [neutralY_modes]
    change Function.HasFiniteSupport (mixedLeft D 0 0 a b c p q r) ∧
      Function.HasFiniteSupport (mixedFirst D 0 0 a b c p q r) ∧
      Function.HasFiniteSupport (mixedSecond D 0 0 a b c p q r) ∧ _
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    simp_rw [smul_sub]
    change (∑ᶠ i : ℕ, mixedLeft D 0 0 a b c p q r i) =
      ∑ᶠ i : ℕ, (mixedFirst D 0 0 a b c p q r i - mixedSecond D 0 0 a b c p q r i)
    rw [finsum_sub_distrib h.2.1 h.2.2.1]
    exact h.2.2.2

end
end D5.S3.VertexAlgebra.LatticeSectorIntertwiner
