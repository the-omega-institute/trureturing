import OmegaMath.NumberTheory.GRH.Lib.ClassField.Places.CyclotomicCharacter
import OmegaMath.NumberTheory.GRH.Lib.ClassField.GaloisCohomology.CupProduct
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand quotient
(known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Herbrand-type index; counting equivariant maps from a lattice to a projective module.
Tate's index formula for the Herbrand quotient of a prime-order action. -/

open Module Nat Submodule AddSubgroup Fint Function LinearMap Matrix MonoidAlgebra Representation

attribute [-simp] map_inv

attribute [local simp] toMatrix_apply Matrix.sum_apply bot_inf_eq finrank_quotient_eq_of_le_torsion

variable {l : ℕ} {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →ₗ[ℤ] B)
  (g : B →ₗ[ℤ] C)

/-- For a linear map f : A → B, the rational number #coker f / #ker f; it is 0 if either group
is infinite. -/
noncomputable def cokerKerIndex : ℚ := Nat.card (B ⧸ f.range) / Nat.card f.ker

lemma cokerKerIndex_comp : cokerKerIndex (g ∘ₗ f) = g.range.cardQuot * ((f.range ⊔ g.ker).cardQuot /
  Nat.card (f.range ⊓ g.ker :)) / Nat.card f.ker ∧ (cokerKerIndex f ≠ 0 ∨ cokerKerIndex g ≠ 0 →
  cokerKerIndex (g ∘ₗ f) = cokerKerIndex f * cokerKerIndex g) := by
  rcases (relIndex_inf_mul_relIndex ⊥ f.range.toAddSubgroup g.ker.toAddSubgroup).symm,
    (relIndex_mul_relIndex ⊥ _ _ bot_le ((f : A →+ B).ker_le_comap (g : B →+ C).ker)).symm
  simp_all [cokerKerIndex, ← cardQuot_apply, cardQuot, SubmoduleElem, range_comp, sup_toAddSubgroup,
    relIndex_ker, index_map, map_toAddSubgroup, AddSubgroup.map_comap_eq,
    ← relIndex_mul_index (toAddSubgroup_mono (@le_sup_left _ _ _ g.ker))]; ring!; aesop

lemma cokerKerIndex_mul_of_exact (hf : Injective f) (h : Exact f g) (hg : Surjective g) :
    cokerKerIndex (l : End ℤ A) ≠ 0 → cokerKerIndex (l : End ℤ B) =
  cokerKerIndex (l : End ℤ A) * cokerKerIndex (l : End ℤ C) := by
  let ψ := (coprod l (-f)).prod (g ∘ₗ fst ..)
  have : Exact ψ (coprod (-g) l) ∧ Exact (f.prod l) ψ := by
    simp_all [Exact, ψ, hg.forall, ← hf.eq_iff]
    use fun b x ↦ by grind [h (l • x - b)], by grind
  rw [← snd_prod f (l : End ..), ← coprod_inr (-g) (l : End ..)]
  convert (cokerKerIndex_comp (ψ.rangeRestrict ∘ₗ inl ..) (fst .. ∘ₗ ψ.range.subtype)).2 ∘ .inl <;>
    simp_all [↓cokerKerIndex_comp, exact_iff, range_inr, range_inl, ← ker_eq_bot, ← range_eq_top,
    range_coprod, sup_comm, inf_comm]
  aesop

/-- If f : A → B has finite kernel and cokernel, then #(A/lA) / #A[l] = #(B/lB) / #B[l], each
side read as 0 when one of its groups is infinite. -/
lemma cokerKerIndex_natCast_eq_of_ne_zero (h : cokerKerIndex f ≠ 0) : cokerKerIndex (l : End ℤ A) =
  cokerKerIndex (l : End ℤ B) := mul_right_cancel₀ h (by
  simp [← (cokerKerIndex_comp ..).2, h, mul_comm]; congr!; aesop)

variable [NeZero l] [Module.Finite ℤ A]

lemma cokerKerIndex_eq_pow_finrank : cokerKerIndex (l : End ℤ A) ≠ 0 ∧ cokerKerIndex (l : End ℤ A) =
  l ^ finrank ℤ A := by erw [cokerKerIndex_natCast_eq_of_ne_zero
  (torsion ..).mkQ (by simp [cokerKerIndex, card_pos.ne', finite_of_fg_torsion]), cokerKerIndex,
  ← index_eq_card, index_range_nsmul]; simp [NeZero.ne, ← natCast_zsmul, SubmoduleElem]

/-- Let a finite group Δ act on a finite set Z, a finitely generated abelian group C and a finite
projective 𝔽_l[Δ]-module B (∑ gτg⁻¹ = 1). If an equivariant C → ℝ^Z has full rank and rank C ≤ #Z,
then #Hom_Δ(C/torsion, B) = #Map_Δ(Z, B). -/
lemma card_hom_lattice_eq_card_equivariant (l : ℕ) [NeZero l] [Module.Finite ℤ C] {Δ Z : Type}
  [Group Δ] [Fintype Δ] [Finite
  B] [MulAction Δ Z] [Fact l.Prime] {σ : Representation ℤ Δ B} {τ : B →+ B} (hτ : ∀ a, ∑ g, σ g (τ
  (σ g⁻¹ a)) = a) [Module (ZMod l) B] {ρ} {Λ : Z → C →ₗ[ℤ] ℝ} (h : ∀ g z y, Λ z (ρ g⁻¹ y) = Λ (g •
  z) y) (hi : LinearIndependent ℝ Λ) (hr : finrank ℤ C ≤ .card Z) : Nat.card {f : IntertwiningMap
  ρ σ // torsion ℤ C ≤ ker f.1} = .card {F : Z → B // ∀ g z, F (g • z) = σ g (F z)} := by
  let c := finBasis (ZMod l) B
  let N g i j : ℤ := (c.repr (σ g (τ (c j))) i).val
  let ρ' := ρ.quotient (torsion ..) fun g _ ↦ .imp (by simp_all [← map_smul])
  have i := hi.of_comp (lcomp ℝ ℝ (mkQ _)) (v := fun z ↦ liftQ (torsion ℤ C) _ fun _ ⟨_, h⟩ ↦ by
    simpa [Submonoid.smul_def] using congr(Λ z $h))
  have := i.finite
  have k {L ι} [AddCommGroup L] [Free ℤ L] [Module.Finite ℤ L] [Finite ι] (b :
    Basis ι ℤ L) ρ : Nat.card (linHom ρ σ).invariants = .card _ ^ ((∑ g, (toMatrix b b (ρ
    g⁻¹))ᵀ.kronecker (of (N g))).charpoly.map (algebraMap _ (ZMod l))).rootMultiplicity 1 := (by
  let π := ((∑ g, ρ.linHom σ g) ∘ₗ .compRight ℤ τ.toIntLinearMap).toAddMonoidHom.toZModLinearMap l
  rw [← charpoly_map, (?_ : map _ _ = _), π.charpoly_toMatrix (((Pi.basis fun _ ↦ c).reindex
   (.sigmaEquivProd ..)).map (b.constr _)), ← finrank_maxGenEigenspace_eq, ← natCard_eq_pow_finrank]
  congr! 3 with x; simp [-mem_invariants]; use (fun _ ↦ ⟨1, by ext; simp_all [π,
    isIntertwiningMap_iff]⟩), (·.rec (·.rec (by bound) (fun _ I _ ↦ (sub_mem_iff_right
    (invariants _) (self_norm_apply _ · _)).1 ∘ I _) x))
  aesop)
  let γ := basisOfLinearIndependentOfCardEqFinrank' _ i (i.fintype_card_le_finrank.antisymm (by
    simp_all [finrank_linearMap]))
  rw [card_congr (.trans (.mk (fun ⟨f, h⟩ ↦ ⟨liftQ _ _ h, (linearMap_qext _ <| f.2 ·)⟩) (⟨·.comp ⟨_,
    fun _ ↦ rfl⟩, le_comap_mkQ _ (ker _)⟩)) (invariantsEquivIntertwiningMap ρ' _).symm.toEquiv),
    k (finBasis ..), ← (k (basis ..) (ofMulAction ..)).symm.trans (card_congr (((basis ..).constr
    ℕ).symm.subtypeEquiv fun _ ↦ inv_surjective.forall.trans (by simp [MonoidAlgebra.lhom_ext'_iff,
    LinearMap.ext_ring_iff, inv_apply_eq_iff])))]
  congr 3
  simp [← (Polynomial.map_injective _ (algebraMap _ ℝ).injective_int).eq_iff, ← charpoly_map]
  convert ((∑ g, TensorProduct.map (lcomp ℝ ℝ (ρ' g⁻¹)) (toLin' (of (N g · ·)))).charpoly_toMatrix
    (.tensorProduct (.ofEquivFun ((finBasis ..).constr ℝ).symm) (Pi.basisFun ..))).trans
    (charpoly_toMatrix _ (γ.tensorProduct (Pi.basisFun ..))).symm <;> ext ⟨⟩ ⟨⟩ <;> simp [mul_comm,
    basis, Finsupp.single_apply, eq_inv_smul_iff, eq_comm, show ∀ g z, (ρ' g⁻¹).lcomp ℝ ℝ (γ z) = γ
    (g • z) by clear * - h; aesop]

open End Polynomial GeneralLinearGroup IsCyclotomicExtension QuotientGroup

set_option synthInstance.maxHeartbeats 200000 in
/-- Tate's index formula: let σ^l = 1 on B, l prime, C → B → B → C (j, σ − 1, s) exact, j
injective, sj = l. With q_A = #(A/lA)/#A[l] and q_C ≠ 0, [C : sB]^{l−1}
q_B = q_C^l. -/
lemma Tate.index_formula {B C} [AddCommGroup B] [AddCommGroup C] (s : B →ₗ[ℤ] C)
  (j : C →ₗ[ℤ] B) {l : ℕ} [Fact l.Prime] (σ : End ℤ B) (iV : cokerKerIndex (l : End ℤ C) ≠ 0) (hσ :
  σ ^ l = 1) (hj : Injective j) (h0 : Exact j ⇑(σ - 1)) (h1 : Exact ⇑(σ - 1) s) (e : s ∘ₗ j = l) :
  s.range.cardQuot ^ (l - 1) * cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ C) ^ l := by
  let t := (σ - 1).rangeRestrict ∘ₗ (σ - 1).range.subtype
  obtain ⟨z, this : s.range.cardQuot * cokerKerIndex t = cokerKerIndex (s ∘ₗ j)⟩ :=
    zeta_spec l ℚ (cycloField l), by
    simp_all [t, SubmoduleElem, ↓cokerKerIndex_comp, exact_iff, sup_comm, inf_comm]
  obtain ⟨u, hu⟩ := (Rat.associated_zeta_sub_one_pow_prime _ z).map
    (z.integralPowerBasis.lift (σ.restrict (by simp) : End ℤ (σ - 1).range) (by
    ext ⟨_, x, ⟨⟩⟩; simpa [cyclotomic_prime, pow_restrict _, ← z.toInteger.minpoly_coe ▸
    cyclotomic_eq_minpoly z Fin.pos', hσ] using congr($(geom_sum_mul σ l) x)))
  simp [← IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have H m : cokerKerIndex (t ^ m * (LinearMap.GeneralLinearGroup.toLinearEquiv u).1) =
    cokerKerIndex t ^ m := by induction m; simp [cokerKerIndex]; erw [_root_.pow_succ', mul_assoc,
    (cokerKerIndex_comp ..).2] <;> grind
  rw [cokerKerIndex_mul_of_exact _ _ hj (by simp_all [exact_iff]) (σ - 1).surjective_rangeRestrict
    iV, (hu ▸ H _ :), mul_left_comm, ← mul_pow, this, e, mul_pow_sub_one NeZero.out]

/-- Let f : A → G and θ : A → C be homomorphisms of abelian groups, C divisible, H a subgroup of
G. If θ is trivial on f⁻¹(H), some homomorphism χ : G → C kills H and has χ∘f = θ. -/
lemma exists_monoidHom_extend {A G C} [CommGroup A] [CommGroup G] [CommGroup C] [d : DivisibleBy
  (Additive C) ℤ] (f : A →* G) (θ : A →* C) H (h : ∀ a, f a ∈ H → θ a = 1) : ∃ χ : G →* C, H ≤
  χ.ker ∧ ∀ a, χ (f a) = θ a := (QZ.exists_extend ((mk' H).comp f).toAdditive θ.toAdditive
  (h · ∘ (eq_one_iff _).1)).elim (⟨_, ·.toMultiplicative.comap_ker _ |>.subst (le_comap_mk' ..), ·⟩)
