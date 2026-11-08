/- GID: D5/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sectors/LatticeSectorFourFieldFullIOReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-target outer collision readout from the original four-field middle numerator. -/
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldRawMiddleCoefficients

/-!
The original Bakalov--Kac, Matsuo--Nagatomo and Carnahan normalizations and
attributions are retained in the suppliers.
proof_shape: actual_four_field_fullIO_middle_readout: content
admission_basis: escape-witness
escape_witness: the joint collision/middle inverse fiber has a finite bound
forced by the original signed numerator coordinates. This identifies the
outer FullIO iterate readout with an eight-index finite contraction of the
same four-field numerator, including negative target coordinates.
The outer clearing data are chosen after fixing the two inner modes; no
uniform truncation of varying fused states is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.LatticeSectorFourFieldFullIOReadout
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeAllStateField
open LatticeSectorIntertwiner LatticeSectorIntertwiner.FiniteSectorObject
open LatticeSectorChannelTransport LatticeSectorFourFieldCommonSeries
open LatticeSectorFourFieldInnerIterate LatticeSectorFourFieldMiddleSpectator
open LatticeSectorFourFieldRawMiddleCoefficients
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedChannelSeries
open FourFieldInnerPolynomial FourFieldMiddlePolynomial SupportedFourFieldMiddleCollision
open FourFieldMiddleLaurentFiber
open StateFieldResidueReconstruction (integerBinomial)
open FieldNormalProductLocality (deltaEnd commutator)
open scoped BigOperators
noncomputable section

/-- The original numerator bounds the collision index jointly with all seven
middle inverse indices. This bound depends on the fixed b,y slice. -/
private theorem middle_collision_tail {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 4) R) (k : ℕ) (a : Fin 4 → ℕ)
    (x b z y : ℤ) (i : ℕ)
    (large : z + b + y + a 1 + a 2 + a 3 + 3 * k < i) :
    middleCoefficient P k a ![x + i, b, z - i, y] = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro h hh
  obtain ⟨_, _, _, _, _, _, bound, _⟩ := middle_bounds k a _ h
    ((mem_middleFiber_iff k a _ h).mp hh)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at bound
  omega

/-- At each finite target coordinate, the cleared channel
(u_r(v_b t))_s(q_y w) is a finite contraction of the original middle
numerator. Its collision index is bounded by the original k,a,b,y data,
rather than a cutoff uniform over fused states. All signed targets occur. -/
theorem actual_four_field_fullIO_middle_readout
    (D : LatticeData) (α β γ η : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η) :
    let c : Fin 4 → Charge D := ![α, β, γ, η]
    let states : Fin 4 → Oscillator D := ![u, v, t, q]
    ∃ k : ℕ,
      (∀ i j : Fin 4, i < j →
        (deltaEnd ^ k) (commutator (labelledFields D c states i)
          (labelledFields D c states j)) = 0) ∧
      ∀ (δ : Charge D) (w : Sector D δ), ∃ a : Fin 4 → ℕ,
        ∃ P : MvPowerSeries (Fin 4) (Oscillator D),
        (∀ (i : Fin 4) (n : ℤ), (a i : ℤ) ≤ n →
          canonical D (c i) δ (states i) n w = 0) ∧
        (∀ (i j l m : Fin 4), ([0, 1, 2, 3] : List (Fin 4)).Perm [i, j, l, m] →
          ∀ e : Exponent 4,
            polynomialAction (clearingPolynomial 4 k) (nestedCanonical D c states δ w i j l m)
              (fun n => e n - a n) = signedExtend P e) ∧
        (∀ e : Exponent 4,
          polynomialAction (innerPolynomial k a)
            (fun d => innerIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst
                (SupportedFourFieldCollision.fourInnerArguments (Oscillator D)) P) e) ∧
        (∀ e : Exponent 4,
          polynomialAction (middlePolynomial k a)
            (fun d => middleIterate D α β γ η δ u v t q w (d 0) (d 1) (d 2) (d 3)) e =
              signedExtend (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) e) ∧
        (∀ e : Exponent 4,
          middleIterate D α β γ η δ u v t q w (e 0) (e 1) (e 2) (e 3) =
            middleCoefficient (MvPowerSeries.subst (middleFourArguments (Oscillator D)) P) k a e) ∧
        ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
          (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
          (M : FiniteSectorObject D) (F : FullIO D α ((β + γ) + (η + δ)) M) (b y : ℤ),
          let f := (fullUniversal D H hHG hGH α ((β + γ) + (η + δ)) M).symm F
          let vb := canonical D β γ v (-b - 1) t
          let qw := canonical D η δ q (-y - 1) w
          let productF := fun x z : ℤ => F.val u (-x - 1)
            (canonical D (β + γ) (η + δ) vb (-z - 1) qw)
          let iterateF := fun r s : ℤ =>
            (fullChannel D H hHG hGH α (β + γ) (η + δ) M F).val
              (canonical D α (β + γ) u (-r - 1) vb) (-s - 1) qw
          let Pm := MvPowerSeries.subst (middleFourArguments (Oscillator D)) P
          ∃ N A B : ℕ, ∃ Q : MvPowerSeries (Fin 2) (M.States D),
            (∀ x z : ℤ,
              clear N productF (x - A) (z - B) = extend Q x z ∧
              clearIterate N A B iterateF x z = extend (collision Q) x z) ∧
            ∀ (r s : ℤ) (ι : Fin M.size),
              (clearIterate N A B iterateF r s) ι =
                ∑ i ∈ Finset.range ((s - B + b + y + a 1 + a 2 + a 3 + 3 * k).toNat + 1),
                  ∑ h ∈ middleFiber k a ![r - A - N + i, b, s - B - i, y],
                    (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
                      (middleWeight k a h •
                        (f.val (signedExtend Pm
                          (middleInput k a ![r - A - N + i, b, s - B - i, y] h))) ι) := by
  classical
  dsimp only
  obtain ⟨k, locality, rest⟩ := actual_four_field_raw_middle_coefficients D α β γ η u v t q
  refine ⟨k, locality, ?_⟩
  intro δ w
  obtain ⟨a, P, truncation, allOrders, inner, middle, raw⟩ := rest δ w
  refine ⟨a, P, truncation, allOrders, inner, middle, raw, ?_⟩
  intro H hHG hGH M F b y
  let f := (fullUniversal D H hHG hGH α ((β + γ) + (η + δ)) M).symm F
  let vb := canonical D β γ v (-b - 1) t
  let qw := canonical D η δ q (-y - 1) w
  let productF := fun x z : ℤ => F.val u (-x - 1)
    (canonical D (β + γ) (η + δ) vb (-z - 1) qw)
  let iterateF := fun r s : ℤ =>
    (fullChannel D H hHG hGH α (β + γ) (η + δ) M F).val
      (canonical D α (β + γ) u (-r - 1) vb) (-s - 1) qw
  let Pm := MvPowerSeries.subst (middleFourArguments (Oscillator D)) P
  have readout (x z : ℤ) : productF x z =
      f.val (middleCoefficient Pm k a ![x, b, z, y]) := by
    have eqF := (fullUniversal D H hHG hGH α ((β + γ) + (η + δ)) M).apply_symm_apply F
    have eq := congrArg (fun J : FullIO D α ((β + γ) + (η + δ)) M =>
      J.val u (-x - 1) (canonical D (β + γ) (η + δ) vb (-z - 1) qw)) eqF
    change f.val (middleIterate D α β γ η δ u v t q w x b z y) = productF x z at eq
    rw [← eq]
    apply congrArg f.val
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using raw ![x, b, z, y]
  obtain ⟨N, A, B, Q, common, inverse, _⟩ := fullIO_supported_channel_transport
    D H hHG hGH α (β + γ) (η + δ) M F u vb qw
  have lower (x z : ℤ) (hz : z < -(B : ℤ)) : productF x z = 0 := by
    exact (inverse x z).trans (ite_eq_right (by omega))
  refine ⟨N, A, B, Q, ?_, ?_⟩
  · intro x z
    exact ⟨(common x z).1, (common x z).2.2⟩
  · intro r s ι
    have collisionLaw := SupportedThreeFieldCollision.signed_cleared_collision
      productF N A B lower Q (fun x z => (common x z).1) r s
    have finiteReadout :
        (∑ᶠ i : ℕ, (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
          productF (r - A - N + i) (s - B - i)) =
        ∑ i ∈ Finset.range ((s - B + b + y + a 1 + a 2 + a 3 + 3 * k).toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
            productF (r - A - N + i) (s - B - i) := by
      apply finsum_eq_sum_of_support_subset
      intro i hi
      by_contra outside
      apply hi
      have large : s - B + b + y + a 1 + a 2 + a 3 + 3 * k < i := by
        simp only [Finset.mem_coe, Finset.mem_range, not_lt] at outside
        have := Int.self_le_toNat (s - B + b + y + a 1 + a 2 + a 3 + 3 * k)
        omega
      change (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
        productF (r - A - N + i) (s - B - i) = 0
      rw [readout, middle_collision_tail Pm k a (r - A - N) b (s - B) y i large,
        map_zero, smul_zero]
    have actualFinite : clearIterate N A B iterateF r s =
        ∑ i ∈ Finset.range ((s - B + b + y + a 1 + a 2 + a 3 + 3 * k).toNat + 1),
          (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - r - 1) i) •
            productF (r - A - N + i) (s - B - i) :=
      (common r s).2.2.trans (collisionLaw.2.symm.trans finiteReadout)
    rw [actualFinite]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [readout]
    simp only [middleCoefficient, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, Finset.smul_sum]
    rfl

/-!
The finite-target readout above is now consumed by an explicit four-object
reassociation statement. The two paths below have the same source and target
FullIO spaces. The first path reassociates from the right by two
`fullChannel`s. The second first transports the middle charge, applies the
other `fullChannel`, and transports the left charge. These are the actual
linear equivalences induced by the universal incoming maps; no pentagon or
analytic sewing principle is added.
-/

private def incomingChargeAssoc (D : LatticeData) {p q : Charge D}
    (M : FiniteSectorObject D) (h : p = q) :
    Incoming D p M ≃ₗ[ℂ] Incoming D q M where
  toFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).symm.trans (f.property a n x)⟩
  invFun f := ⟨f.val, by
    intro a n x
    have e := congrArg (fun δ : Charge D => action D δ a n x) h
    exact (congrArg f.val e).trans (f.property a n x)⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply Subtype.ext; rfl
  map_add' f g := rfl
  map_smul' c f := rfl

private def fullInputChargeAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    {p q β : Charge D} (M : FiniteSectorObject D) (h : p = q) :
    FullIO D p β M ≃ₗ[ℂ] FullIO D q β M :=
  (fullUniversal D H hHG hGH p β M).symm.trans
    ((incomingChargeAssoc D M (by simpa [h])).trans
      (fullUniversal D H hHG hGH q β M))

private def fullMiddleChargeAssoc (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D α ((β + γ) + δ) M :=
  (fullUniversal D H hHG hGH α (β + (γ + δ)) M).symm.trans
    ((incomingChargeAssoc D M (by rw [add_assoc β γ δ])).trans
      (fullUniversal D H hHG hGH α ((β + γ) + δ) M))

/-- The right-associated four-object channel path. -/
def fourFieldShortPath (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D ((α + β) + γ) δ M :=
  (fullChannel D H hHG hGH α β (γ + δ) M).trans
    (fullChannel D H hHG hGH (α + β) γ δ M)

/-- The middle-first four-object channel path. -/
def fourFieldAlternatePath (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    FullIO D α (β + (γ + δ)) M ≃ₗ[ℂ] FullIO D ((α + β) + γ) δ M :=
  (fullMiddleChargeAssoc D H hHG hGH α β γ δ M).trans
    ((fullChannel D H hHG hGH α (β + γ) δ M).trans
      (fullInputChargeAssoc D H hHG hGH M (add_assoc α β γ).symm))

theorem fourField_reassociation_path_eq (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α β γ δ : Charge D) (M : FiniteSectorObject D) :
    fourFieldShortPath D H hHG hGH α β γ δ M =
      fourFieldAlternatePath D H hHG hGH α β γ δ M := by
  apply LinearEquiv.ext
  intro F
  apply (fullUniversal D H hHG hGH ((α + β) + γ) δ M).symm.injective
  simp only [fourFieldShortPath, fourFieldAlternatePath, LinearEquiv.trans_apply]
  simp [add_assoc, fullMiddleChargeAssoc, fullInputChargeAssoc,
    incomingChargeAssoc, fullChannel]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  rfl

theorem actual_four_field_fullIO_reassociation
    (D : LatticeData) (α β γ η : Charge D)
    (u : Sector D α) (v : Sector D β) (t : Sector D γ) (q : Sector D η) :
    ∀ (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
        (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
        (M : FiniteSectorObject D),
        fourFieldShortPath D H hHG hGH α β γ η M =
          fourFieldAlternatePath D H hHG hGH α β γ η M := by
  have _readout := actual_four_field_fullIO_middle_readout D α β γ η u v t q
  intro H hHG hGH M
  exact fourField_reassociation_path_eq D H hHG hGH α β γ η M

#print axioms actual_four_field_fullIO_middle_readout
#print axioms fourField_reassociation_path_eq
#print axioms actual_four_field_fullIO_reassociation
end
end D5.S3.VertexAlgebra.LatticeSectorFourFieldFullIOReadout
