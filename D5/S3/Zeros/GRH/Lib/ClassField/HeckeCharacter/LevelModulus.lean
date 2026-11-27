/- GID: D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LevelModulus
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LevelModulus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.HeckeCharacter.LevelModulus. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/HeckeCharacter/LevelModulus.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.LevelForms
import D5.S3.Zeros.GRH.Lib.Weil.CompactLift.BranchingPeriod
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ModularDataDecay
import D5.S3.Zeros.GRH.Lib.Weil.DualPair.ThetaIntegralLaws
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

Part of: Contravariant form on Weyl's lattice, Fischer product, irreducibility under U(n) (known
result; see Lib.Adelic.CuspForms.DeltaForms).

This file: Surjective reduction of the level group; tame characters modulo a modulus. Polarisation
of determinant powers through the Fischer pairing, from unitary to all matrices. The modulus M^c Q
built from the chosen places and its support. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Ideal Set AutChar Fint MatMul Matrix Modulus MulChar MvPolynomial NumberField Subgroup
  Ideal.IsPrime

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {𝔪 : Modulus E}

/-- Every g in GL_n(O_E/𝔪) is the reduction modulo 𝔪 of an element of K₀ supported on the places
dividing 𝔪 and their conjugates. -/
lemma exists_reductionK₀_eq (g : GL n 𝔪.ResRing) : ∃ k, ↑k ∈ Gf.supportedOn n 𝔪.places ∧
  𝔪.reductionK₀ k = g := by
  choose M hM using (𝔪.reduction_surjective <| g · ·)
  use ⟨_, (atSplits_mem_Kf (by grind -abstractProof [disjoint_places_star]) _).2 fun w ↦ ⟨(isUnit_of_mapMatrix
    (IsLocalRing.residue _) ⟨g.map (modulusResidue _ (mem_toFinset.1 w.2)), funext₂
    (by simp [← hM]; tauto)⟩).unit, rfl⟩⟩, (by grind -abstractProof [atSplits_mem_supportedOn, coe_toFinset]); ext
  exact hM .. ▸ reduction_congr _ fun w
    h ↦ by set_option synthInstance.maxHeartbeats 200000 in
      simpa using! congr($(atPlace_atSplits _ _ ⟨w, by simpa⟩) _ _)

/-- A chosen lift of g ∈ GL_n(O_E/𝔪) to K₀, with component 1 outside the places dividing 𝔪 and their
conjugates. -/
noncomputable def liftMod (g : GL n 𝔪.ResRing) := (exists_reductionK₀_eq g).choose

@[simp] lemma reductionK₀_liftMod (g : GL n 𝔪.ResRing) : 𝔪.reductionK₀ (liftMod g) =
  g := by grind [liftMod]

@[simp] lemma reductionK₀_surjective : Function.Surjective (𝔪.reductionK₀ (n := n)) :=
  (⟨_, reductionK₀_liftMod ·⟩)

/-- The level cut out by a subgroup H of GL_n(O_E/𝔪): the elements of K_0 (`Kf`) whose
reduction modulo 𝔪 lies in H, as a subgroup of G_f. -/
noncomputable abbrev Modulus.levelOfSubgroup 𝔪 H :=
  (Subgroup.comap (reductionK₀ 𝔪) H).map (Kf E n).subtype

lemma Modulus.principalLevel_le_levelOfSubgroup {a} {H : Subgroup (GL n 𝔪.ResRing)} (h :
  a ∈ 𝔪.ideal) : principalLevel n a ≤ 𝔪.levelOfSubgroup H := fun _ k ↦
  ⟨_, H.ker_le_comap _ (map_eq_one_of_principalLevel k (by simpa [← RingHom.mem_ker])), rfl⟩

instance {H : Subgroup (GL n 𝔪.ResRing)} : IsLevel (𝔪.levelOfSubgroup H) :=
  ⟨map_subtype_le _, isOpen_mono (principalLevel_le_levelOfSubgroup 𝔪.ideal.absNorm_mem)
  (isOpen_principalLevel (by simp [ne_bot, absNorm_eq_zero_iff]))⟩

lemma Modulus.stdLevelIndex_levelOfSubgroup {H : Subgroup (GL n 𝔪.ResRing)} :
  stdLevelIndex (𝔪.levelOfSubgroup H) = H.index := by
  simp [relIndex, subgroupOf, comap_map_eq, index_comap_of_surjective]

attribute [local simp] Kf.reduceAt reductionK₀ inv_apply_eq_inv finprod_eq_prod_of_fintype

variable {a : NumberField.RingOfIntegers E} in
lemma Modulus.mem_principalLevel_iff (e : 𝔪.ideal = span {a}) k : k.1 ∈ principalLevel n a ↔
  𝔪.reductionK₀ k = 1 := by simpa [principalLevel, *, Kf.map_eq_one, ↓reduction_eq_zero_iff,
  mem_span_singleton, dvd_def, Subtype.ext_iff] using .rfl

/-- The multiplicative character x ↦ ∏_{w∣𝔪} ψ_w(x mod w) of O_E/𝔪, for characters ψ_w of the
residue fields. -/
@[simps -isSimp] noncomputable def Modulus.charOfTamePart 𝔪 (ψ : ∀ w : FinPlace E, MulChar (ResField
  w) ℂ) := MulChar.mk ⟨⟨fun x ↦ ∏ᶠ w : places 𝔪, ψ _ (modulusResidue _ w.2 x), by simp⟩, by simp⟩
  (Quot.ind fun _ ↦ (fun ⟨M, _, c⟩ ↦ by simpa [prod_eq_zero_iff, apply_eq_zero_iff] using
  ⟨⟨_, .under .., NeZero.out⟩, le_comap_of_map_le (by simp), algebraMap_ResField_eq_zero.2 c⟩) ∘
  exists_max_ideal_of_mem_nonunits)

/-- 𝔪 ≠ (1), ν has weight e and tame part (ψ_w) nontrivial exactly at the primes w dividing 𝔪,
and χ = ∏ψ_w on O_E/𝔪. -/
def IsTameFor {E : Type} [Field E] [CMType E]
    (𝔪 : Modulus E) (ν : AutChar E) e (χ : MulChar 𝔪.ResRing ℂ) :=
  Nonempty 𝔪.places ∧ ∃ ψ, ν.HasWeight e ψ ∧ (∀ w, ψ w ≠ 1 ↔ w ∈ 𝔪.places) ∧ χ = 𝔪.charOfTamePart ψ

lemma AutChar.HasWeight.apply_det_eq_charOfTamePart {E : Type} [Field E] [CMType E] {𝔪 : Modulus E}
    {ν : AutChar E} {e :
  InfinitePlace E → ℤ} {s : n → _} {ψ} (a : HasWeight ν e ψ) (b : ∀ w ∉ 𝔪.places, ψ w = 1) k :
  ν.1 (detFin s k.1) = 𝔪.charOfTamePart ψ (𝔪.reductionK₀ k).1.det := by
    simp [a.apply_det_eq_prod Subtype.val_injective (by simpa), charOfTamePart, det_apply]

lemma IsTameFor.inv {E : Type} [Field E] [CMType E] {𝔪 : Modulus E}
    {ν e χ} (h : IsTameFor 𝔪 ν e χ) : IsTameFor 𝔪 ν⁻¹ (-e)
  χ⁻¹ := by aesop (add simp [IsTameFor, charOfTamePart_apply], safe HasWeight.inv)

lemma IsTameFor.mul {E : Type} [Field E] [CMType E] {𝔪 : Modulus E}
    {ν e χ} (h : IsTameFor 𝔪 ν e χ) {μ d} (a : μ.HasWeight d 1) :
    IsTameFor 𝔪 (ν * μ) (e + d) χ := by grind [IsTameFor, HasWeight.mul]

lemma IsTameFor.apply_det {E : Type} [Field E] [CMType E] {𝔪 : Modulus E}
    {ν : AutChar E} {e : InfinitePlace E → ℤ} {χ :
  MulChar 𝔪.ResRing ℂ} {s : n → _} (h : IsTameFor 𝔪 ν e χ) k : ν.1 (detFin s k.1) =
  χ (𝔪.reductionK₀ k).1.det := by grind [IsTameFor, HasWeight.apply_det_eq_charOfTamePart]

variable {Φ n a S : Type} [Fintype Φ] [Fintype n] [CommRing S] [Algebra ℂ S] [Fintype a]
  {ι : Φ → Type} [∀ τ, Fintype (ι τ)] (Y : Φ → n → a → S) (η : ∀ τ, ι τ → Matrix a n ℂ)

/-- The element ∏_τ ∏_k det(η_{τk} Y_τ) of the ℂ-algebra S, for n×a matrices Y_τ over S and
complex a×n matrices η_{τk}. -/
noncomputable def pairedDetProd := ∏ τ, ∏ k, ((η τ k).map (algebraMap ℂ S) * of (Y τ)).det

/-- Polarisation: suppose M(q(uᵀY)) = K(u) for all tuples u of unitary n×n matrices. Then ⟨q,
∏_τ det(rows r)^{#ι_τ}⟩·M(∏ det(η_{τk}Y_τ)) = ⟨K, ∏ det(η_{τk}X_τ)⟩ in the Fock pairing, X_τ
being the columns r of the generic n×n matrix. -/
lemma fockPairing_polarisation (M : S →ₗ[ℂ] ℂ) {r} q K (h : ∀ u : Φ → USign 1, M (aeval (fun (τ, j,
  k) ↦ ∑ i, (u τ).1.1 i j • Y τ i k) q) = eval (fun (τ, i, j) ↦ (u τ).1.1 i j) K) : fockPairing ℂ q
  (∏ τ, letterMinor τ r id ^ Fintype.card (ι τ)) * M (pairedDetProd Y η) =
  fockPairing ℂ K (pairedDetProd (X ⟨·, ·, r ·⟩) η) := by
  choose t e using (algebraTensorAlgEquiv ℂ S).surjective (linSubst (of fun (σ, j, k)
    (τ, c, i) ↦ ite (σ = τ ∧ j = i) (Y τ c k) 0)ᵀ (MvPolynomial.map (algebraMap ..) q))
  obtain ⟨s, rfl⟩ := t.exists_finset
  have e P x := congr((M (fockPairing S $e (MvPolynomial.map (algebraMap ℂ S) P)),
    M (aeval (algebraMap ℂ S ∘ x) $e)))
  simp [← eval₂_comp, ← map_fockPairing, ↓← fockPairing_linSubst, linSubst, Fintype.sum_prod_type,
    ite_and, aeval_bind₁, Algebra.algebraMap_eq_smul_one, forall_and] at *
  rw [← (sub_eq_zero.1 (funext fun x ↦ .trans ((eval_rename (Prod.rec .mk) ..).symm.trans
    (PolyRep.zariski_dense_unitary (x ⟨·, ·, ·⟩) _ fun u hu ↦ ?_) :) ?_) : ∑ i ∈ s, M i.1 • i.2 =
    K)] <;> simp [*, mul_comm (M _), eval_rename]
  rw [← smul_eq_mul, ← map_smul, Algebra.smul_def, map_fockPairing, mul_comm,
    ← (fockPairing S).smul_right]
  simp only [letterMinor, pairedDetProd, map_prod, ← card_univ, ← prod_const, ← C_mul',
    RingHom.map_det, ← prod_mul_distrib, ← det_mul, ← (of _).det_transpose]
  simp [det_apply', Matrix.mul_apply]
  exact h (U.of (by simp) _ <| by simp [hu ·])

omit [IsCMField E]

lemma prod_places_le_iff {ι} [Fintype ι] {u : ι → FinPlace E} {w} : ∏ i, (u i).1 ≤ w.1 ↔ ∃ i, u i =
  w := by simp [prod_le, IsMaximal.eq_iff_le, ne_top, (u _).ext_iff]

/-- The modulus M^c·Q, or M^c if b is false, where M and Q are the products of the primes in the
two families of S. -/
noncomputable def LevelPlaces.levelModulus (S : LevelPlaces E) c (b : _ := true) := Modulus.mk
    ((∏ i, (S.chosenPlace i).1) ^ c * ite b (∏ i, (S.twistPlace i).1) 1)
  (by simp [← absNorm_eq_zero_iff, prod_eq_zero_iff, ite_eq_iff]) (by rcases S.apart, c, b with ⟨⟨⟩,
  ⟨⟩, ⟨⟩⟩ <;> simp_all [IsPrime.mul_le, pow_le_iff, _root_.prod_places_le_iff, ne_top] <;> grind)

lemma places_levelModulus [IsCMField E] {S : LevelPlaces E} {c : ℕ} [NeZero c] :
  (S.levelModulus c).places = range (S.chosenPlace ⊕ᵥ S.twistPlace) :=
  Set.ext (·.2.mul_le.trans (by simp [pow_le_iff NeZero.out, _root_.prod_places_le_iff]))

/-- For a place i among the chosen and twist places, the reduction homomorphism from the residue
ring modulo M^c·Q (c ≥ 1) to the residue field at that place. -/
noncomputable abbrev levelResidueAt {S : LevelPlaces E} {c : ℕ} [NeZero c] i :=
  modulusResidue (S.levelModulus c) (places_levelModulus.ge ⟨i, rfl⟩)

/-- Chinese remainder theorem: if the ideal of 𝔪 is the product of distinct primes w_i, two
matrices over O_E/𝔪 are equal if and only if their reductions at every w_i are equal. -/
lemma Modulus.matrix_ext_modulusResidue {ι} [Fintype ι] {u : ι → FinPlace E} [IsCMField E] {𝔪 :
  Modulus E} (hu : u.Injective) {a b} {x y : Matrix a b _} (e : 𝔪.ideal = ∏ i, (u i).1 := by
  simp [LevelPlaces.levelModulus]) : x = y ↔ ∀ i, let r := modulusResidue 𝔪 (w := u i) (by simp_all
    [Modulus.places, _root_.prod_places_le_iff]); x.map r = y.map r := by
  simp [← ext_iff, @forall_comm ι]; congr!; obtain ⟨⟨⟩, ⟨⟩⟩ := x .., y ..
  erw [Ideal.Quotient.eq]; simp [*, mem_prod_finPlace_iff, ← algebraMap_ResField_eq_zero]; rfl
