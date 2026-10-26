/- GID: D5/S3/VertexAlgebra/Lattice/NormFourCommutant
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourCommutant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal norm-four annihilator vertex algebra and coset conformal action. -/

import D5.S3.VertexAlgebra.Lattice.NormFourCosetVirasoro

/-!
The norm-four state and its OPE are supplied by NormFourVirasoroVector and
NormFourCosetVirasoro: Shimakura, arXiv:1202.6107, (1.3), attributing the formula
to Dong--Mason--Zhu, Theorem 6.3. The ambient lattice fields follow Bakalov--Kac,
math/0402315, section 4.1. The concrete subtype inheritance below adapts
LatticeInvolution's fixed-field construction, not its theta closure proof.
Imported residue and normal-product sources retain their Scott Carnahan,
Matsuo--Nagatomo and Kytola attribution and Apache 2.0 license notices.
The new closure uses the actual mode commutator on the full production carrier.
This is an ungraded e-annihilator vertex algebra with a coset conformal state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourCommutant
open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeActualVertexAlgebra LatticeActualStateFieldCalculus
open NormFourVirasoroVector FieldNormalProductLocality
open LatticeActualConformalState LatticeSugawaraVirasoro LatticeSugawaraCurrents
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators VertexOperator
noncomputable section

/-- The literal intersection of every nonnegative actual e-mode kernel. -/
def space (D : LatticeData) (α : Charge D) (s : ℂ) : Submodule ℂ (Carrier D) where
  carrier := {v | ∀ j : ℤ, 0 ≤ j → mu D (vector D α s) j v = 0}
  zero_mem' := by intro j hj; exact map_zero _
  add_mem' := by
    intro u v hu hv j hj
    change ((Y D (vector D α s))[[j]]) (u + v) = 0
    rw [map_add]
    change mu D (vector D α s) j u + mu D (vector D α s) j v = 0
    rw [hu j hj, hv j hj, add_zero]
  smul_mem' := by
    intro z v hv j hj
    change ((Y D (vector D α s))[[j]]) (z • v) = 0
    rw [map_smul]
    change z • mu D (vector D α s) j v = 0
    rw [hv j hj, smul_zero]

private theorem restricted_mode_closed (D : LatticeData) (α : Charge D) (s : ℂ)
    (u v : Carrier D) (hu : u ∈ space D α s) (hv : v ∈ space D α s) (n : ℤ) :
    ((Y D u)[[n]]) v ∈ space D α s := by
  intro j hj
  have commute : ((Y D (vector D α s))[[j]]) * ((Y D u)[[n]]) -
      ((Y D u)[[n]]) * ((Y D (vector D α s))[[j]]) = 0 := by
    rw [mode_commutator]
    have vanish (k : ℕ) : commutatorTerm D (vector D α s) u j n k = 0 := by
      simp [commutatorTerm, hu (k : ℤ) (by omega)]
    simp only [vanish, finsum_zero]
  have h := LinearMap.congr_fun commute v
  change mu D (vector D α s) j (((Y D u)[[n]]) v) -
    ((Y D u)[[n]]) (mu D (vector D α s) j v) = 0 at h
  rw [hv j hj, map_zero, sub_zero] at h
  exact h

private theorem vacuum_mem (D : LatticeData) (α : Charge D) (s : ℂ) :
    vacuum D ∈ space D α s := by
  intro j hj
  exact stateField_creativity D (vector D α s) j hj

/-- The actual ambient vacuum, with no norm or sign hypothesis. -/
def restrictedVacuum (D : LatticeData) (α : Charge D) (s : ℂ) : ↥(space D α s) :=
  ⟨vacuum D, vacuum_mem D α s⟩

private theorem restricted_translation_closed (D : LatticeData) (α : Charge D) (s : ℂ)
    (v : Carrier D) (hv : v ∈ space D α s) : translation D v ∈ space D α s := by
  rw [translation_as_mode]
  exact restricted_mode_closed D α s v (vacuum D) hv (vacuum_mem D α s) (-2)

abbrev CommutantCarrier (D : LatticeData) (α : Charge D) (s : ℂ) := ↥(space D α s)

-- Keep the actual subtype group instance available while elaborating its endomorphisms.
local instance commutantCarrierGroup
    (D : LatticeData) (α : Charge D) (s : ℂ) : AddCommGroup (CommutantCarrier D α s) :=
  (space D α s).addCommGroup

def restrictedTranslation
    (D : LatticeData) (α : Charge D) (s : ℂ) : Module.End ℂ (CommutantCarrier D α s) where
  toFun v := ⟨translation D v.val, restricted_translation_closed D α s v.val v.property⟩
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' s a := by apply Subtype.ext; exact map_smul _ _ _

private def restrictedMode
    (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) (n : ℤ) :
    Module.End ℂ (CommutantCarrier D α s) where
  toFun b := ⟨((Y D a.val)[[n]]) b.val,
    restricted_mode_closed D α s a.val b.val a.property b.property n⟩
  map_add' b c := by apply Subtype.ext; exact map_add _ _ _
  map_smul' s b := by apply Subtype.ext; exact map_smul _ _ _

/-- Lower truncation is inherited statewise from the actual ambient field. -/
private def restrictedField (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) :
    VertexOperator ℂ (CommutantCarrier D α s) :=
  VertexOperator.of_coeff (fun k => restrictedMode D α s a (-k-1)) (by
    intro b
    refine ⟨((HahnModule.of ℂ).symm ((Y D a.val) b.val)).order, ?_⟩
    intro k hk
    by_contra h
    have hz : ((Y D a.val)[[-k-1]]) b.val = 0 := by
      apply VertexOperator.ncoeff_eq_zero_of_lt_order
      omega
    exact hk (Subtype.ext hz))

@[simp] private theorem restrictedField_ncoeff
    (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) (n : ℤ) :
    (restrictedField D α s a)[[n]] = restrictedMode D α s a n := by
  rw [restrictedField, VertexOperator.ncoeff_of_coeff]
  rw [show -(-n-1)-1 = n by omega]

def restrictedY (D : LatticeData) (α : Charge D) (s : ℂ) :
    CommutantCarrier D α s →ₗ[ℂ] VertexOperator ℂ (CommutantCarrier D α s) where
  toFun := restrictedField D α s
  map_add' a b := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro c
    simp only [VertexOperator.coeff_eq_ncoeff, map_add, Pi.add_apply,
      LinearMap.add_apply, restrictedField_ncoeff]
    apply Subtype.ext
    change ((Y D (a.val + b.val))[[-k-1]]) c.val =
      ((Y D a.val)[[-k-1]]) c.val + ((Y D b.val)[[-k-1]]) c.val
    simp only [map_add, Pi.add_apply, LinearMap.add_apply]
  map_smul' s a := by
    apply HVertexOperator.coeff_inj
    funext k
    apply LinearMap.ext
    intro c
    simp only [VertexOperator.coeff_eq_ncoeff, map_smul, Pi.smul_apply,
      LinearMap.smul_apply, restrictedField_ncoeff]
    apply Subtype.ext
    change ((Y D (s • a.val))[[-k-1]]) c.val = s • ((Y D a.val)[[-k-1]]) c.val
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]

@[simp] private theorem restrictedY_mode_val
    (D : LatticeData) (α : Charge D) (s : ℂ) (a b : CommutantCarrier D α s) (n : ℤ) :
    (((restrictedY D α s a)[[n]]) b).val = ((Y D a.val)[[n]]) b.val := by
  change (((restrictedField D α s a)[[n]]) b).val = _
  rw [restrictedField_ncoeff]; rfl

private theorem restricted_creation
    (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) :
    ((restrictedY D α s a)[[-1]]) (restrictedVacuum D α s) = a := by
  apply Subtype.ext
  exact stateField_creation D a.val

private theorem restricted_creativity
    (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) (n : ℤ)
    (hn : 0 ≤ n) : ((restrictedY D α s a)[[n]]) (restrictedVacuum D α s) = 0 := by
  apply Subtype.ext
  simpa only [restrictedY_mode_val, restrictedVacuum, Submodule.coe_zero] using
    stateField_creativity D a.val n hn

private theorem restricted_vacuum_field (D : LatticeData) (α : Charge D) (s : ℂ) :
    restrictedY D α s (restrictedVacuum D α s) = FieldNormalProduct.identityField := by
  apply HVertexOperator.coeff_inj
  funext k
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  rw [VertexOperator.coeff_eq_ncoeff, restrictedY_mode_val]
  change ((Y D (vacuum D))[[-k-1]]) b.val = _
  rw [stateField_vacuum]
  simp [FieldNormalProduct.identityField, VertexOperator.ncoeff_of_coeff]
  split_ifs <;> rfl

private theorem restricted_covariance
    (D : LatticeData) (α : Charge D) (s : ℂ) (a : CommutantCarrier D α s) (n : ℤ) :
    restrictedTranslation D α s * ((restrictedY D α s a)[[n]]) -
      ((restrictedY D α s a)[[n]]) * restrictedTranslation D α s =
        -(n : ℂ) • ((restrictedY D α s a)[[n-1]]) := by
  apply LinearMap.ext
  intro b
  apply Subtype.ext
  have h := LinearMap.congr_fun (stateField_covariance D a.val n) b.val
  simpa [restrictedTranslation, Module.End.mul_apply] using h

/-- Subtype inclusion identifies every iterated locality coefficient. -/
private theorem restricted_delta_transport (D : LatticeData) (α : Charge D) (s : ℂ)
    (f : ℤ → ℤ → Module.End ℂ (CommutantCarrier D α s))
    (g : ℤ → ℤ → Module.End ℂ (Carrier D))
    (h : ∀ m n b, (f m n b).val = g m n b.val)
    (N : ℕ) (m n : ℤ) (b : CommutantCarrier D α s) :
    ((delta^[N] f) m n b).val = (delta^[N] g) m n b.val := by
  induction N generalizing f g m n with
  | zero => exact h m n b
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change ((delta^[N] f) (m+1) n b - (delta^[N] f) m (n+1) b).val =
      (delta^[N] g) (m+1) n b.val - (delta^[N] g) m (n+1) b.val
    simp only [Submodule.coe_sub]
    rw [ih f g h (m+1) n, ih f g h m (n+1)]

private theorem restricted_locality
    (D : LatticeData) (α : Charge D) (s : ℂ) (a b : CommutantCarrier D α s) :
    ∃ N : ℕ, delta^[N]
      (FieldNormalProductLocality.commutator (restrictedY D α s a) (restrictedY D α s b)) = 0 := by
  obtain ⟨N, hN⟩ := LatticeAllStateLocality.stateField_locality D a.val b.val
  refine ⟨N, ?_⟩
  funext m n
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have h := restricted_delta_transport D α s
    (FieldNormalProductLocality.commutator (restrictedY D α s a) (restrictedY D α s b))
    (FieldNormalProductLocality.commutator (Y D a.val) (Y D b.val))
    (by intro u v w; simp [FieldNormalProductLocality.commutator,
      Module.End.mul_apply]) N m n c
  rw [hN] at h
  simpa using h

/-- Inclusion preserves zero exactly, hence the genuine support, for every family. -/
private theorem restricted_support_transport (D : LatticeData) (α : Charge D) (s : ℂ) {I : Type*}
    (f : I → CommutantCarrier D α s) :
    Function.support (fun i => (f i).val) = Function.support f := by
  ext i
  simp only [Function.mem_support]
  exact Subtype.val_injective.ne_iff' rfl

private theorem restricted_finite_transport (D : LatticeData) (α : Charge D) (s : ℂ) {I : Type*}
    (f : I → CommutantCarrier D α s)
    (h : Function.HasFiniteSupport (fun i => (f i).val)) :
    Function.HasFiniteSupport f := by
  simpa only [Function.HasFiniteSupport, restricted_support_transport] using h

private theorem restricted_finsum_val
    (D : LatticeData) (α : Charge D) (s : ℂ) {I : Type*} (f : I → CommutantCarrier D α s) :
    (∑ᶠ i, f i).val = ∑ᶠ i, (f i).val :=
  (space D α s).subtype.toAddMonoidHom.map_finsum_of_injective Subtype.val_injective f

/-- Full p,q,r : Int identity and all three actual finite supports. -/
private theorem restricted_borcherds
    (D : LatticeData) (α : Charge D) (s : ℂ) (a b c : CommutantCarrier D α s) (p q r : ℤ) :
    let mu : CommutantCarrier D α s → ℤ → CommutantCarrier D α s → CommutantCarrier D α s :=
      fun a n b => ((restrictedY D α s a)[[n]]) b
    let left : ℕ → CommutantCarrier D α s :=
      fun i => integerBinomial p i • mu (mu a (r+i) b) (p+q-i) c
    let first : ℕ → CommutantCarrier D α s := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) • mu a (p+r-i) (mu b (q+i) c)
    let second : ℕ → CommutantCarrier D α s := fun i =>
      (((-1 : ℂ)^i)*integerBinomial r i) •
        (StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c))
    Function.HasFiniteSupport left ∧ Function.HasFiniteSupport first ∧
      Function.HasFiniteSupport second ∧
        (∑ᶠ i : ℕ, left i) = ∑ᶠ i : ℕ,
          (((-1 : ℂ)^i)*integerBinomial r i) •
            (mu a (p+r-i) (mu b (q+i) c) -
              StateFieldResidueReconstruction.epsilon r • mu b (q+r-i) (mu a (p+i) c)) := by
  dsimp only
  have h := (actualVertexAlgebra D).borcherds a.val b.val c.val p q r
  dsimp only [actualVertexAlgebra] at h
  refine ⟨restricted_finite_transport D α s _ ?_, restricted_finite_transport D α s _ ?_,
    restricted_finite_transport D α s _ ?_, ?_⟩
  · simpa only [Submodule.coe_smul, restrictedY_mode_val] using h.1
  · simpa only [Submodule.coe_smul, restrictedY_mode_val] using h.2.1
  · simpa only [Submodule.coe_smul, restrictedY_mode_val] using h.2.2.1
  · apply Subtype.ext
    simpa only [restricted_finsum_val, Submodule.coe_smul, Submodule.coe_sub,
      restrictedY_mode_val] using h.2.2.2

/-- The actual ungraded vertex algebra on the literal nonnegative e-mode annihilator. -/
def restrictedVertexAlgebra
    (D : LatticeData) (α : Charge D)
    (s : ℂ) : StateFieldVertexAlgebra (CommutantCarrier D α s) where
  stateField := restrictedY D α s
  vacuum := restrictedVacuum D α s
  translation := restrictedTranslation D α s
  vacuum_field := restricted_vacuum_field D α s
  creation := restricted_creation D α s
  creativity := restricted_creativity D α s
  translation_vacuum := by
    apply Subtype.ext
    exact translation_kills_vacuum D
  covariance := restricted_covariance D α s
  locality := restricted_locality D α s
  borcherds := restricted_borcherds D α s


/-- Actual vacuum, every integer state-field coefficient, and actual T preserve
precisely the intersection of all nonnegative e-mode kernels. -/
theorem actual_closure (D : LatticeData) (α : Charge D) (s : ℂ) :
    vacuum D ∈ space D α s ∧
    (∀ u v : Carrier D, u ∈ space D α s → v ∈ space D α s →
      ∀ n : ℤ, mu D u n v ∈ space D α s) ∧
    (∀ v : Carrier D, v ∈ space D α s → translation D v ∈ space D α s) ∧
    (∀ (u v : CommutantCarrier D α s) (n : ℤ),
      (((restrictedY D α s u)[[n]]) v).val = mu D u.val n v.val) :=
  ⟨vacuum_mem D α s, restricted_mode_closed D α s,
    restricted_translation_closed D α s, restrictedY_mode_val D α s⟩

private theorem coset_mem (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α : Charge D) (ha : bilinear D α α = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    NormFourCosetVirasoro.cosetVector D H α s ∈ space D α s := by
  obtain ⟨h0, h1, h2, h3, ht⟩ := self_products D α ha s hs
  intro j hj
  have self : mu D (vector D α s) j (vector D α s) =
      (if j = 0 then translation D (vector D α s)
       else if j = 1 then (2 : ℂ) • vector D α s
       else if j = 3 then (1 / 4 : ℂ) • vacuum D else 0) := by
    by_cases z : j = 0
    · subst j; simpa using h0
    · by_cases o : j = 1
      · subst j; simpa using h1
      · by_cases t : j = 3
        · subst j; simpa using h3
        · by_cases two : j = 2
          · subst j; simpa using h2
          · simpa [z, o, t] using ht j (by omega)
  change ((Y D (vector D α s))[[j]]) (omega D H - vector D α s) = 0
  rw [map_sub]
  change mu D (vector D α s) j (omega D H) - mu D (vector D α s) j (vector D α s) = 0
  rw [((NormFourCosetVirasoro.mixed_products D H hHG hGH α ha s).1 j hj).2, self, sub_self]

/-- The actual omega-e state in the literal annihilator; both inverse-Gram
identities, norm four and the original sign equation are retained. -/
def cosetVector (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α : Charge D) (ha : bilinear D α α = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    CommutantCarrier D α s :=
  ⟨NormFourCosetVirasoro.cosetVector D H α s, coset_mem D H hHG hGH α ha s hs⟩

/-- All integer Virasoro-indexed coefficients of the actual restricted coset field. -/
def cosetMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α : Charge D) (ha : bilinear D α α = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (m : ℤ) : Module.End ℂ (CommutantCarrier D α s) :=
  ((restrictedY D α s (cosetVector D H hHG hGH α ha s hs))[[m + 1]])

/-- Full ambient coefficient binding, coset translation on this literal space,
and the all-integer Virasoro law with central charge rank(D)-1/2. -/
theorem coset_conformal (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (α : Charge D) (ha : bilinear D α α = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    (∀ (n : ℤ) (v : CommutantCarrier D α s),
      (((restrictedY D α s (cosetVector D H hHG hGH α ha s hs))[[n]]) v).val =
        mu D (NormFourCosetVirasoro.cosetVector D H α s) n v.val) ∧
    cosetMode D H hHG hGH α ha s hs (-1) = restrictedTranslation D α s ∧
    (∀ m n : ℤ,
      cosetMode D H hHG hGH α ha s hs m * cosetMode D H hHG hGH α ha s hs n -
          cosetMode D H hHG hGH α ha s hs n * cosetMode D H hHG hGH α ha s hs m =
        ((m : ℂ) - (n : ℂ)) • cosetMode D H hHG hGH α ha s hs (m + n) +
          (if m + n = 0 then
            (((D.rank : ℂ) - 1 / 2) / 12 * ((m : ℂ)^3 - (m : ℂ))) •
              (1 : Module.End ℂ (CommutantCarrier D α s)) else 0)) := by
  have coeff (m : ℤ) (v : CommutantCarrier D α s) :
      (cosetMode D H hHG hGH α ha s hs m v).val =
        NormFourCosetVirasoro.cosetMode D H α s m v.val := by
    exact restrictedY_mode_val D α s _ v (m + 1)
  have ambient := NormFourCosetVirasoro.coset_virasoro D H hHG hGH α ha s hs
  refine ⟨?_, ?_, ?_⟩
  · intro n v
    exact restrictedY_mode_val D α s _ v n
  · apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [coeff, ambient.2.1 (-1)]
    change sugawaraMode D H (-1) v.val - mode D α s (-1) v.val = translation D v.val
    rw [sugawaraMode_minus_one_eq_translation D H hHG hGH]
    have kill : mode D α s (-1) v.val = 0 := v.property 0 (by omega)
    rw [kill, sub_zero]
  · intro m n
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have law := LinearMap.congr_fun (ambient.2.2.2 m n) v.val
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      coeff]
    by_cases hmn : m + n = 0
    · simpa only [hmn, ite_true, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_smul] using law
    · simpa only [hmn, ite_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        Submodule.coe_zero] using law

end
end D5.S3.VertexAlgebra.Lattice.NormFourCommutant
