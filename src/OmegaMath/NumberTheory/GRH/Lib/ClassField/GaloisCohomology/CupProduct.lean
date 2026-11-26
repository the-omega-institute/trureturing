import OmegaMath.NumberTheory.GRH.Lib.ClassField.GaloisCohomology.DiscreteUnits
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles (known
result; see Lib.ClassField.LocalDuality.CrystallineDuality).

This file: Cup product on cocycles, Cartier dual module, annihilators and their orders. -/

noncomputable section


open Function AddSubgroup QuotientAddGroup AddMonoidHom DFunLike Nat DiscreteModule
variable {R R' S} (Γ) [CommRing R] [CommRing R'] [CommRing S] [Group Γ] [TopologicalSpace Γ]
  {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] [IsAlgClosed Ω]
  {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The multiplicative group Ω^×, written additively, as a discrete module with its continuous
action of Γ. -/
abbrev unitsModule [IsProGalois Γ K Ω] := of (@unitsRep Γ ..) (continuous_prod_of_discrete_right.2
  fun x ↦ ((isLocallyConstant_smul _).desc (unitsRep · x) _ Units.val_injective).continuous)

instance [Finite A] : Finite (A →+ DiscreteUnits Ω) := .of_equiv _ toMultiplicativeLeft.symm

instance : DivisibleBy (DiscreteUnits Ω) ℤ := @AddGroup.divisibleByIntOfDivisibleByNat _ _
  (divisibleByOfSMulRightSurj _ _ (swap (·.exists_nsmul)))

variable {Γ} (b : A →+ B →+ C)
attribute [local simp] ext_iff LE.le forall_mk funext_iff continuous_prod_of_discrete_right

/-- For a biadditive pairing b : A × B → C and a subgroup L of A, the subgroup of y in B with
b(x, y) = 0 for all x in L. -/
def pairingAnnihilator L :=
  (b.comp (AddSubgroup.subtype L)).flip.ker.copy {y | ∀ x ∈ L, b x y = 0} (by aesop)

instance : TopologicalSpace (A →+ B) := ⊥

instance : DiscreteTopology (A →+ B) := ⟨rfl⟩

/-- Let b : A × B → C be biadditive with C isomorphic to ℚ/ℤ. For a subgroup L of A with
annihilator L^⊥ in B, #L^⊥·#L = #B·#(L ∩ left kernel of b), infinite orders being read as 0. -/
lemma card_pairingAnnihilator_mul_card (e : QZ ≃+ C) L : .card (pairingAnnihilator b L) * .card L =
  .card B * Nat.card ↥(b.ker ⊓ L) := let β := b.comp L.subtype
  by erw [pairingAnnihilator, β.flip.ker.copy_eq, ← addSubgroupOf_map_subtype, card_subtype _ β.ker]
     grind [show β.flip.ker.index = β.ker.index by apply dvd_antisymm <;> exact (by_cases (⟨0, ·⟩)
       fun h ↦ (index_dvd_of_le (by simp)).trans (@card_hom_QZ _ _ (finite_of_card_ne_zero h) ▸
       card_dvd_of_injective _ (kerLift_injective ((kerLift _).flip.compr₂ e.symm)))),
       card_mul_index]

section

variable (W : DiscreteModule S Γ) (M : DiscreteModule R Γ) (N :
  DiscreteModule R' Γ) (b : M →+ N →+ W) (e : ∀ g x y, b (M.ρ g x) (N.ρ g y) = W.ρ g (b x y))

/-- The cup product Z¹(M) × Z¹(N) → H²(W) of an equivariant pairing b : M × N → W: the class of
(g, h) ↦ b(x(g), g y(h)). -/
def cupProduct : Z1 M.ρ →+ Z1 N.ρ →+ W.H2 := (mk' (fun x ↦ mk' (fun y ↦ (⟨fun p ↦ b (x.1 p.1)
    (N.ρ p.1 (y.1 p.2)), y.2.rec fun _ _ ↦ x.2.imp (by fun_prop) (by aesop)⟩ : Z2 W.ρ)) (by simp))
    (by simp)).compr₂ (mk' _)

variable {W M N}

/-- The cup product of 1-cocycles is anticommutative: y ∪ x for the flipped pairing equals −(x ∪
y) in H²(W). -/
lemma cupProduct_flip : ∀ x y, cupProduct _ _ _ b.flip (swap <| e ·) y x = -cupProduct W M N b e x y
  | ⟨x, _, _⟩, ⟨y, _, _⟩ => eq_iff_sub_mem.2 ⟨fun g ↦ -b (x g) (y g), by fun_prop, by
    simp_all; intros; abel⟩

end

variable [IsProGalois Γ K Ω] (M : DiscreteModule R Γ)

/-- For finite M, the dual M^* = Hom(M, Ω^×): the discrete Γ-module over ℤ of additive maps from
M to Ω^× (written additively), with (gf)(m) = g f(g⁻¹m). -/
abbrev DiscreteModule.cartierDual [Finite M] := let W := unitsModule Γ; of ⟨⟨fun g ↦ toIntLinearMap
    (mk' (comp (W.ρ g) <| comp · (M.ρ g⁻¹) : _ → M →+ W) (by simp)), by simp⟩, by simp⟩ (.congr (by
                     simp; fun_prop) (leftInverse_invFun coe_injective ∘' _))

/-- For finite M with dual M^* = Hom(M, Ω^×), the cup product Z¹(M^*) × Z¹(M) → H²(Γ, Ω^×) for
the evaluation pairing (f, m) ↦ f(m). -/
abbrev DiscreteModule.evalCup [Finite M] := cupProduct _ M.cartierDual M (.id _) (by simp)

variable {M} {N : DiscreteModule R Γ} [Finite M] [Finite N]

/-- The dual of an equivariant map u : M → N of finite modules: the equivariant map Hom(N, Ω^×)
→ Hom(M, Ω^×) sending f to f ∘ u. -/
abbrev DiscreteModule.Hom.cartierDualMap (u : M.Hom N) : N.cartierDual.Hom M.cartierDual :=
  ⟨(compHom' u).toIntLinearMap, by simp [u.isIntertwining]⟩
