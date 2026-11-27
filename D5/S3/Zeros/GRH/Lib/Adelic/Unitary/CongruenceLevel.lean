/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Unitary/CongruenceLevel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Unitary/CongruenceLevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Unitary.CongruenceLevel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Unitary/CongruenceLevel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.Groups.CompactMean
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ColumnLattices
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.LocalComponents
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: congruence subgroups and level structures of adelic groups. Here levels are taken
in the unitary group of the identity form. They are preimages of subgroups of the reductions at
finitely many split places, or principal levels of a global modulus. Source: V. Platonov, A.
Rapinchuk, ch. 3 and 5; B. H. Gross, Algebraic modular forms, Israel J. Math. 113 (1999) 61-93.

Known result: the Iwasawa–Bruhat decomposition of GL_n over a local field, and the Iwahori
factorisation. Row operations write every element as unitriangular times monomial times an element
of the pro-p Iwahori group, and that group factors into upper and lower parts. Only existence is
proved, with no double cosets of the Iwahori group and no uniqueness. Source: Iwahori–Matsumoto,
Publ. IHES 25 (1965); Casselman, Introduction to admissible representations of p-adic groups: GL_n
(notes), §13.

Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Reduction maps, principal levels, levels cut out by reductions at split places; index.
Parahoric and pro-p Iwahori groups, dominant cone, exponents, multiplicativity of U-operators.
Principal congruence subgroups: neighbourhood basis, index bound, quotients of profinite
integers. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

section

open Function Matrix NumberField IsLocalRing Subgroup Kf Gf Ideal Valued algebraMap
variable {n ι R S E : Type*} [Fintype n] [CommRing R] [CommRing S] [Field E] [NumberField E]
  {w : FinPlace E} {a b : 𝓞 E}

lemma GL_map_surjective (f : R →+* S) [IsLocalHom f] : Surjective f →
    Surjective (GeneralLinearGroup.map (n := n) f) := (surjective_units_map_of_local_ringHom _
  ·.comp_left.comp_left ⟨by simp [↓isUnit_iff_isUnit_det, ↓← f.map_det]⟩)

/-- The reduction homomorphism from GL_n(O_w) to GL_n of the residue field at w. -/
def reduceGL := intGL.map (n := n) (O := v.integer) (S := ResField w) (residue (LocInt w))

lemma reduceGL_surjective : Surjective (reduceGL (n := n) (w := w)) :=
  (GL_map_surjective (residue (LocInt _)) residue_surjective).comp (⟨⟨_, ·, rfl⟩, rfl⟩)

lemma isUnit_algebraMap_finAdele (h : a ≠ 0) : IsUnit (a : 𝔸f E) :=
  .map (algebraMap E _) (.mk0 (a : E) (by simpa))

/-- For an integer a of E, a finite adele y lies in aÔ if and only if y lies in Ô and |y|_u ≤
|a|_u at every finite place u dividing a. -/
lemma mem_span_iff_valuation_le {y} : y ∈ Ô E ∙ ↑a ↔ y ∈ Ô E ∧ ∀ u, a ∈ u.1 → v (y u) ≤
  u.intValuation a := by
  simp [↓exists_eq_mul_iff_v_le, mem_Ô, ← forall_and]; peel with u
  erw [v_algebraMap_eq_intValuation a]; grind [u.intValuation_le_one a, u.intValuation_eq_one_iff]

variable [IsCMField E] (n a) {f : Ô E →+* S}

@[simp] lemma Kf.map_apply g i j : map n f g i j = f ⟨_, mem_Kf.1 g.2 i j⟩ := rfl

lemma Kf.map_eq_one {g} : map n f g = 1 ↔
    ∀ i j, f (⟨_, mem_Kf.1 g.2 i j⟩ - ⟨_, mem_Kf.1 (one_mem _) i j⟩) = 0 := intGL.map_eq_one

/-- The principal level K(a): the subgroup of g in K₀ = `Kf` with all entries of g − 1 in
aÔ, for an integer a of E. -/
def principalLevel : Subgroup (Gf E n) := .copy ((congruenceGL (Ô E ∙ _) id).subgroupOf _) {g ∈
  Kf .. | ∀ i j, ∃ y ∈ _, (g.1.1 - 1) i j = algebraMap _ _ a * y} (by aesop (add simp congruenceGL))

variable {n a k} (hk : k ∈ principalLevel n a) {k : Kf E n}

lemma map_eq_one_of_principalLevel (e : f a = 0) : map n f ⟨_, hk.1⟩ = 1 := (map_eq_one n).2
  fun i j ↦ (RingHom.ker f).mem_of_dvd (by simpa [dvd_def, Subtype.ext_iff] using! hk.2 ..) e

omit [IsCMField E] in
lemma isOpen_congruenceGL_span (h : a ≠ 0) : (congruenceGL (Ô E ∙ ↑a) (@id n)).IsOpen
  := isOpen_congruenceGL isOpen_Ô
  (Eq.subst (by aesop) ((isUnit_algebraMap_finAdele h).isOpenMap_smul _ isOpen_Ô))

lemma isOpen_principalLevel (h : a ≠ 0) : (principalLevel n a).IsOpen :=
  (copy_eq ..).symm.subst (isOpen_congruenceGL_span h).preimage_val

lemma principalLevel_le_Kf : principalLevel n a ≤ Kf .. := fun _ ↦ (·.1)

instance [Fact (a ≠ 0)] : IsLevel (principalLevel n a) :=
  ⟨principalLevel_le_Kf, isOpen_principalLevel Fact.out⟩

lemma principalLevel_le_of_dvd : a ∣ b → principalLevel n b ≤ principalLevel n a := fun ⟨c, e⟩ _ ↦
  .imp_right (forall₂_imp
  fun _ _ ⟨_, h, r⟩ ↦ ⟨_, mul_mem (coe_mem_Ô c) h, by simpa [e, mul_assoc] using! r⟩)

/-- Known result: Congruence subgroups and level structures of adelic groups. -/
lemma exists_principalLevel_subset {s} (h : s ∈ nhds 1) : ∃ M ≠ 0,
  SetLike.coe (principalLevel n (Nat.cast M : 𝓞 E)) ⊆ s
  := ((mem_nhds_induced ..).1 h).elim fun _ b ↦ (exists_congruenceGL_subset b.1).imp fun _ ↦
  .imp_right fun c _ k ↦ b.2 (c _ (by simpa [principalLevel, congruenceGL] using! k))

instance : NonarchimedeanGroup (Gf E n) := ⟨fun _ h ↦ (exists_principalLevel_subset h).rec
    (⟨⟨principalLevel n ·, isOpen_principalLevel (by aesop)⟩, ·.2⟩)⟩

lemma Kf.reduceAt_eq_of_atPlace {t} (h : k.1.atPlace w = .map (LocInt w).subtype t) : reduceAt w k =
  .map (residue _) t := congr(reduceGL ⟨$h, t, by aesop⟩)

lemma Kf.reduceAt_eq_one_of_atPlace : k.1.atPlace w = 1 →
  reduceAt w k = 1 := by simpa using reduceAt_eq_of_atPlace (t := 1)

variable (w : ι → FinPlace E) (H : Subgroup (∀ i, GL n (ResField (w i))))

/-- The family w of finite places of the CM field E is injective and no w j is the conjugate of
any w i; in particular no w i is its own conjugate. -/
class IsConjApart where
  injective : Injective w
  star_ne i j : star (w i) ≠ w j

/-- The homomorphism from K₀ to ∏_i GL_n(k_{w_i}) given by reduction modulo each place of the
family w_i. -/
def Kf.reduceFamily : Kf E n →* ∀ i, GL n (ResField (w i)) := .pi (reduceAt <| w ·)

/-- The subgroup of G_f of elements of K₀ whose reductions modulo the places w_i form an element
of the subgroup H of ∏_i GL_n(k_{w_i}). -/
def levelOf := (H.comap (reduceFamily w)).map (Kf ..).subtype

variable {w H}

lemma levelOf_le_Kf : levelOf w H ≤ Kf .. := map_subtype_le _

lemma mem_levelOf {g} : g ∈ levelOf w H ↔ ∃ h, reduceFamily w ⟨g, h⟩ ∈ H := by simp [levelOf]

variable (w H) in
/-- The homomorphism from the level `levelOf` w H to H given by reduction modulo the places w_i. -/
def levelOf.reduction : levelOf w H →* H :=
  ((reduceFamily w).comp (inclusion levelOf_le_Kf)).codRestrict _ (mem_levelOf.1 ·.2 |>.2)

lemma inf_trivialOn_le_levelOf : Kf .. ⊓ trivialOn n (.range w) ≤ levelOf w H :=
  fun _ k ↦ ⟨⟨_, k.1⟩, H.ker_le_comap _ (funext fun _ ↦ reduceAt_eq_one_of_atPlace (by aesop)), rfl⟩

lemma principalLevel_le_levelOf (h : ∀ i, a ∈ (w i).1) : principalLevel n a ≤ levelOf w H :=
  fun _ k ↦ ⟨_, H.ker_le_comap _ (funext fun _ ↦ map_eq_one_of_principalLevel k (by aesop)), rfl⟩

variable [Finite ι]

lemma isOpen_levelOf : (levelOf w H).IsOpen :=
  isOpen_mono (principalLevel_le_levelOf (mem_iInf.1 (absNorm_mem _))) (isOpen_principalLevel
  (mod_cast (Finite.of_injective _ (quotientInfToPiQuotient_inj _)).card_pos.ne'))

instance : IsLevel (levelOf w H) := ⟨levelOf_le_Kf, isOpen_levelOf⟩

@[simp] lemma relIndex_ne_zero_of_isLevel K [h : IsLevel K] : K.relIndex (Kf E n) ≠ 0 :=
  isCompact_Kf.relIndex_ne_zero h.2

variable [h : IsConjApart w]

omit [Finite ι] in
lemma reduceFamily_atSplit i (k : Kw n _) : reduceFamily w ⟨atSplit (h.2 i i) k, by simp⟩ =
    Pi.mulSingle i (reduceGL k) := eq_update_iff.2 ⟨reduceAt_eq_of_atPlace (atPlace_atSplit ..),
  fun _ e ↦ reduceAt_eq_one_of_atPlace (atPlace_atSplit_of_ne _ _ (h.1.ne e) (h.2 _ _))⟩

lemma exists_reduceFamily_eq s : ∃ k, k.1 ∈ supportedOn n (.range w) ∧ reduceFamily w k = s :=
  (((supportedOn ..).subgroupOf _).map _).pi_mem_of_mulSingle_mem s fun i ↦ ⟨_, by simp_all
  [eq_comm, atPlace_atSplit_of_ne], surjInv_eq reduceGL_surjective (s i) ▸ reduceFamily_atSplit ..⟩

/-- Known result: Congruence subgroups and level structures of adelic groups. -/
lemma relIndex_levelOf : (levelOf w H).relIndex (Kf ..) = H.index := (congrArg _ (comap_map_eq_self
  (by simp))).trans (H.index_comap_of_surjective (exists_reduceFamily_eq · |>.imp (by simp)))

end

section

open Finset Equiv IsLocalRing Matrix Valued WithZero

attribute [-simp] _root_.map_add _root_.map_sub

variable {n R : Type*} [Fintype n] [CommRing R]

/-- The homomorphism sending a permutation σ to the permutation matrix in GL_n(R) that maps e_i
to e_{σ(i)}. -/
abbrev permGL : Perm n →* GL n R := permMatrixHom.toHomUnits

lemma permGL_mem_intGL σ {O : Subring R} : permGL σ ∈ intGL n O := ⟨permGL σ, by aesop⟩

lemma diagGL_mul_permGL (t : n → Rˣ) σ : diagGL t * permGL σ = permGL σ * diagGL (t ∘ σ) := by aesop

attribute [local simp] Perm.inv_def BlockTriangular diagonal_apply Matrix.single transvection
  PEquiv.mul_toMatrix_toPEquiv PEquiv.toMatrix_mul_apply Units.val_inj mem_intGL_iff_det zero_lt_iff

attribute [simp] Representation.inv_apply_eq_iff

variable (σ : Perm n) {i j : n} (h : i ≠ j) {F : Type*} [Field F] [Valued F ℤᵐ⁰]

lemma permGL_mul_transvectionGL (a : R) : permGL σ * transvectionGL h a =
  transvectionGL (σ.injective.ne h) a * permGL σ := by aesop

instance : IsLocalRing 𝒪[F] := inferInstance

@[simp high] lemma residue_eq_zero_iff_lt {a} :
    residue 𝒪[F] a = 0 ↔ v a.1 < 1 := residue_eq_iff_valuation_sub_lt_one.trans (by simp)

@[local simp] lemma residue_eq_one_iff_lt {a} : residue 𝒪[F] a = 1 ↔ v (a.1 - 1) < 1 :=
  residue_eq_iff_valuation_sub_lt_one

attribute [local grind .] Valuation.zero_iff mul_lt_of_lt_of_le_one one_pos zero_le zero_lt_iff

variable {g : GL n F} [CompactSpace 𝒪[F]] (P : GL n F → Prop) [LinearOrder n]

instance : Finite 𝓀[F] := have := @integer.isPrincipalIdealRing_of_compactSpace F; inferInstance

/-- The open subgroup of the g in GL_n(𝒪) satisfying P, where on GL_n(𝒪) the property P means
that the reduction modulo 𝔭 lies in the subgroup H. -/
def residuePreimage (H : Subgroup _) (e : ∀ k, intGL.map (residue 𝒪[F]) k ∈ H ↔ P k.1) :
    OpenSubgroup (GL n F) := ⟨((H.comap (intGL.map (residue _))).map (Subgroup.subtype _)).copy {g ∈
  intGL .. | P g} (by aesop), (congruenceGL (v.ltSubmodule 1) id).isOpen_mono (fun g ⟨a, _⟩ ↦ ⟨a, by
  rw [← e ⟨g, a⟩, intGL.map_eq_one.2]; simp; simpa⟩)
  (isOpen_congruenceGL (isOpen_integer F) (by simpa using! isOpen_ball F 1))⟩

/-- For a level function b on the indices, the parahoric subgroup of the g in GL_N(𝒪) with g_ij
∈ 𝔭 whenever b(j) < b(i). -/
def blockParahoric {N} (b : ℕ → ℕ) := (residuePreimage (fun g : GL (Fin N) F ↦ ∀ i j,
  b j.1 < b i.1 → v (g i j) < 1) (parabolic (b ·)) (by simp [parabolic])).1

variable {P : GL n F → Prop} (ρ : Rep ℂ (GL n F)) [IsSmoothRep ρ.ρ] (ξ : (n → Fˣ) →* ℂˣ) {t : n →
  Fˣ}

/-- The monoid of dominant elements of the torus: families t of units of F with |t_i| ≤ |t_j|
for i ≤ j. -/
def dominantTorus : Submonoid (n → Fˣ) :=
  ⟨⟨{t | Monotone (v <| t · |>.1)}, by simpa using .mul'⟩, by tauto⟩

omit [LinearOrder n] in
lemma isCompact_residuePreimage {H e} : IsCompact (residuePreimage P H e).carrier :=
  (isCompact_intGL
  (isCompact_iff_compactSpace.2 ‹_›)).of_isClosed_subset (residuePreimage ..).isClosed inf_le_left

instance {N b} : CompactSpace (@blockParahoric F _ _ N b) := isCompact_residuePreimage.compactSpace

/-- The pro-p Iwahori subgroup I₁ of GL_n(𝒪): matrices that are upper triangular with ones on the
diagonal modulo the maximal ideal. -/
def proIwahori := (residuePreimage (fun g : GL n F ↦ (∀ i j, j < i → v (g i j) < 1) ∧ ∀ i,
  v (g i i - 1) < 1) (unitriangular id _) (by simp [apply_ite]; grind)).1

instance : CompactSpace (proIwahori : Subgroup (GL n F)) := isCompact_residuePreimage.compactSpace

omit [CompactSpace 𝒪[F]] in
lemma isOpen_proIwahori : (proIwahori : Subgroup (GL n F)).IsOpen := (residuePreimage ..).2

/-- An exponent: a linear form l invariant under the pro-p Iwahori subgroup I₁, with l(ρ(diag
t)x) = ξ(t) l(x) for t dominant and x fixed by I₁. -/
abbrev IsExponent (l : ρ →ₗ[ℂ] ℂ) := ∀ ⦃t⦄, t ∈ dominantTorus → ∀ x,
  l (ρ (diagGL t) (compactMean ρ.ρ proIwahori x)) = ξ t * l x

/-- x is a nonzero vector fixed by the pro-p Iwahori subgroup I₁ with U_t x = ξ(t) x for all
dominant t, U_t of level I₁. -/
def IsIwahoriEigen x := x ≠ 0 ∧ x ∈ levelSpace ρ.ρ proIwahori ∧ ∀ t ∈ dominantTorus,
  compactMean ρ.ρ proIwahori (ρ (diagGL t) x) = (ξ t).1 • x

/-- The normalised absolute value on F^×, as a character with complex values: x ↦ q^{−ord x}, q
the order of the residue field. -/
def normAbsChar : Fˣ →* ℂˣ := .mk' (fun x ↦ .mk0 (Nat.card 𝓀[F]) NeZero.out ^ (v x.1).log)
    (by simp [_root_.zpow_add])

/-- The bijection sending a family (θ_i), 0 ≤ i < N, of characters of F^× to the character t ↦ ∏
θ_i(t_i)|t_i|^{N−1−i} of the diagonal torus. -/
def torusChar {N} := (Equiv.mulRight fun i : Fin N ↦ normAbsChar (F := F) ^ i.rev.1).trans
    (Pi.monoidHomMulEquiv ..).symm.1

@[simp] lemma torusChar_mulSingle {N θ} (i : Fin N) (x : Fˣ) : torusChar θ (Pi.mulSingle i x) =
  θ i x * normAbsChar x ^
  i.rev.1 := by simp [torusChar, Pi.monoidHomMulEquiv, Pi.mulSingle_apply, apply_ite]

omit [CompactSpace 𝒪[F]] in
lemma exists_proIwahori_coe_eq (M : Matrix n n F) (a : ∀ i j, v (M i j) ≤ 1) (h :
  (∀ i j, j < i → v (M i j) < 1) ∧ ∀ i, v (M i i - 1) < 1) : ∃ g ∈ proIwahori, g.1 = M :=
  ⟨_, ⟨⟨.mk'' (of (⟨_, a · ·⟩)) (.of_map (residue _) _ (by simp_all [RingHom.map_det,
  det_of_isUpperTriangular, residue_eq_one_iff_lt.2])), rfl⟩, h⟩, rfl⟩

omit [CompactSpace 𝒪[F]] in
@[local simp] lemma mem_proIwahori : g ∈ proIwahori ↔ (∀ i j, v (g i j) ≤ 1) ∧ (∀ i, ∀ j < i,
  v (g i j) < 1) ∧ ∀ i, v (g i i - 1) < 1 :=
  ⟨.imp_left (mem_intGL.1 · |>.1), by simpa using exists_proIwahori_coe_eq g.1⟩

section

omit [CompactSpace 𝒪[F]]

lemma mem_proIwahori_iff_of_unitriangular (u : g ∈ unitriangular id _) :
    g ∈ proIwahori ↔ ∀ i j, i < j → v (g i j) ≤ 1 := by simp_all; grind

lemma transvectionGL_mem_proIwahori {a : F} (H : v a < 1 ∨ v a ≤ 1 ∧ i < j) :
  transvectionGL h a ∈ proIwahori := by simp; grind

omit [LinearOrder n] in
lemma diagGL_mem_intGL (h : ∀ i, v (t i).1 = 1) : diagGL t ∈ intGL n 𝒪[F] := by aesop

lemma v_diag_eq_one_of_mem_proIwahori (h : g ∈ proIwahori) j :
  v (g j j) = 1 := by simpa using v.map_one_add_of_lt (h.2.2 j)

/-- Iwasawa and Bruhat decompositions at once: every g in GL_n(F) is u·t·σ·k with u upper
unitriangular over F, t diagonal, σ a permutation matrix and k in the pro-p Iwahori
subgroup.

Known result: Iwasawa–Bruhat decomposition of GL_n over a local field; Iwahori factorisation. -/
lemma exists_iwasawa_bruhat (g : GL n F) : ∃ u ∈ unitriangular id F,
  (∃ t σ, (diagGL t * permGL σ)⁻¹ * (u⁻¹ * g) ∈ proIwahori) ∧
  (g ∈ proIwahori → u ∈ proIwahori ∧ ∀ i j, i < j → (u⁻¹ * g) i j = 0) := by
  have ⟨m, u, k, p, h⟩ : ∃ m, g / m ∈ unitriangular id F ∧ (g ∈ proIwahori → m ∈ proIwahori) ∧ ∃ p :
    Perm n, ∀ i ∈ univ, let x := m i (p i)
    x ≠ 0 ∧ (∀ l, v (m i l) < v x ∨ v (m i l) = v x ∧ p i ≤ l) ∧ ∀ r < i, m r (p i) = 0 :=
      univ.induction_on_min ⟨g, by simp⟩ fun a s h ⟨m, u, k, p, _⟩ ↦ by
    have ⟨j, _⟩ := exists_minimal_of_wellFoundedLT _ (univ.exists_max_image (v ∘ m a) ⟨a, by simp⟩)
    use .mk'' (updateCol 1 a fun r ↦ ite (r < a) (-m r j / m a j) (diagonal 1 r a)) ?_ * m,
      div_mul_eq_div_div_swap g .. ▸ div_mem u ?_, (mul_mem ?_ <| k ·), swap (p a) j * p <;>
      simp [← cramer_apply, updateCol_apply, mul_apply, apply_ite v, sum_ite,
      filter_eq', swap_apply_def] <;> grind [v_diag_eq_one_of_mem_proIwahori, div_one, Minimal,
      mem_proIwahori.1 ∘ k, m.det_ne_zero, det_eq_zero_of_row_eq_zero a, le_zero_iff]
  refine ⟨_, u, ⟨(.mk0 _ <| h · (by simp) |>.1), p⁻¹, ?_⟩, (⟨div_mem · (k ‹_›), ?_⟩)⟩ <;> simp
    [← map_inv, mul_assoc] <;> grind [inv_mul_le_one₀, inv_mul_lt_one₀,
    v_diag_eq_one_of_mem_proIwahori, mem_proIwahori]

lemma diagGL_conj_mem_proIwahori (k : g ∈ proIwahori) (h : g.1.BlockTriangular (v <| t · |>.1)) :
  diagGL t * g * (diagGL t)⁻¹ ∈
  proIwahori := by simp_all [← map_inv, mul_inv_le_iff₀', mul_inv_lt_iff₀']; grind
  [mul_le_of_le_of_le_one, mul_lt_of_lt_one_right, mul_zero, Units.ne_zero]

lemma exists_unipotent_conj_mem_proIwahori (ht : t ∈ dominantTorus) (h : g ∈ proIwahori) :
    ∃ u ∈ unitriangular id F ⊓ proIwahori, (diagGL t)⁻¹ * (u⁻¹ * g) * diagGL t ∈ proIwahori :=
  (exists_iwasawa_bruhat g).imp fun _ _ ↦ by refine ⟨?_,
  diagGL_conj_mem_proIwahori (t := t⁻¹) ?_ ?_⟩ <;> simp_all [mul_mem, inv_lt_inv₀, ht.reflect_lt]

lemma conj_unitriangular_mem_proIwahori (ht : t ∈ dominantTorus) (hu :
  g ∈ unitriangular id F ⊓ proIwahori) : diagGL t * g * (diagGL t)⁻¹ ∈ proIwahori :=
  diagGL_conj_mem_proIwahori hu.2 (by simp_all; grind [ht.reflect_lt])

end

/-- For a smooth representation of GL_n(F), dominant t, t' and x fixed by the pro-p Iwahori
subgroup I₁, the operators U_t = (mean over I₁)∘ρ(diag t) satisfy U_t U_{t'} x = U_{tt'} x. -/
@[local simp] lemma iwahori_operator_mul {ρ : Rep ℂ (GL n F)} [IsSmoothRep ρ.ρ] {t t' : n → _} {x}
    (ht : t ∈ dominantTorus) (ht' : t' ∈ dominantTorus) (hx : x ∈ levelSpace ρ.ρ proIwahori) :
  compactMean ρ.ρ proIwahori (ρ (diagGL t) (compactMean ρ.ρ proIwahori (ρ (diagGL t') x))) =
  compactMean ρ.ρ proIwahori (ρ (diagGL (t * t')) x) := by rw [map_compactMean_of_factor _ fun _ k ↦
  (exists_unipotent_conj_mem_proIwahori ht' k).imp fun _ ↦
  .imp (conj_unitriangular_mem_proIwahori ht) (by simpa using hx ⟨_, ·⟩)] <;> simp_all

/-- The monoid homomorphism t ↦ U_t from dominant torus elements to endomorphisms of the vectors
fixed by the pro-p Iwahori subgroup. -/
def iwahoriHeckeHom : @dominantTorus n F _ _ _ →* Module.End ℂ (levelSpace ρ.ρ proIwahori) :=
    ⟨⟨fun t ↦ (compactMean .. * ρ (diagGL t)).restrict fun _ _ ↦
  compactMean_mem_levelSpace _, by aesop⟩, by aesop⟩

end

attribute [-simp] IsUnit.dvd

open Nat Circle NumberField Ideal Quotient RingOfIntegers Subgroup Kf algebraMap
variable {E} [Field E] [NumberField E] {n} [Fintype n] {a b : 𝓞 E} (h : a ≠ 0) {ι} [Fintype ι]
  {w : ι → FinPlace E}

attribute [local simp] Subtype.ext_iff map_eq_one mem_span_singleton dvd_def principalLevel

/-- A continuous character χ : G → S¹ of a nonarchimedean topological group G is trivial on a
neighbourhood of 1. -/
lemma char_eventually_eq_one {G} [Group G] [TopologicalSpace G] [N : NonarchimedeanGroup G] (χ :
  G →* Circle) (h : Continuous χ) : ∀ᶠ k in nhds 1, χ k = 1 := (N.2 _ (h.tendsto' _ _ χ.map_one
  (hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) ⟨⟩))).rec fun K a ↦ .mono K.mem_nhds_one
  fun _ b ↦ eq_one_of_forall_pow_mem_centeredArc_pi_div_two (by grind [a <| pow_mem b ·])

lemma card_GL_le R [CommRing R] [Finite R] : Nat.card (GL n R) ≤ .card R ^ Fintype.card n ^ 2 :=
  (card_le_card_of_injective _ Units.val_injective).trans (by simp [Matrix, card_pi, sq, pow_mul])

lemma dvd_iff_reduceAt_eq_zero (H : ∀ {v : FinPlace E}, a ∈ v.1 → v.intValuation a = .exp (-1)) y :
    ↑a ∣ y ↔ ∀ w, a ∈ w.1 → _root_.reduceAt w y = 0 := by
  simpa +contextual [H, ← WithZero.lt_mul_exp_iff_le,
    ← WithZero.exp_add] using! @mem_span_iff_valuation_le _ _ _ a y.1

lemma mem_prod_finPlace_iff (hw : w.Injective) {x} : x ∈ ∏ i, (w i).1 ↔ ∀ i, x ∈ (w i).1 := by
  rw [prod_eq_iInf_of_pairwise_isCoprime] <;> simp_all [Set.Pairwise, (w _).isCoprime_of_ne, hw.ne]

include h

lemma dvd_iff_Ô : (a : Ô E) ∣ b ↔ a ∣ b := ⟨fun ⟨_, _⟩ ↦ ⟨⟨_, algebraMap_mem_Ô.1 (by simp_all
  [← mul_assoc, ← map_mul _ _⁻¹])⟩, ext (mul_inv_cancel_left₀ (h <| ext ·) _).symm⟩, map_dvd _⟩

/-- If an ideal I of Ô contracts to the ideal J of 𝓞_E and J contains a nonzero element a, then
𝓞_E/J → Ô/I is bijective. -/
lemma bijective_quot_Ô {I J} (k : Ideal.comap (algebraMap _ (Ô E)) I = J) (ha : a ∈ J) :
    (⇑(quotientMap I _ k.ge)).Bijective := ⟨quotientMap_injective' k.le, Quot.ind
  (exists_dvd_sub_algebraMap h · |>.rec (⟨·, SModEq.sub_mem.2 <| mem_of_dvd _ · (k.ge ha)⟩))⟩

/-- An ideal I of Ô that contains a nonzero element a of 𝓞_E is generated by its contraction to
𝓞_E. -/
lemma map_under_Ô {I} (hI : algebraMap _ (Ô E) a ∈ I) : (under (𝓞 E) I).map (algebraMap ..) = I :=
  map_comap_le.antisymm fun x ↦ by grind [exists_dvd_sub_algebraMap h x, dvd_def, sub_sub_self,
    Submodule.sub_mem_iff_left, mul_mem_right, Ideal.mem_map_of_mem, mem_under]

lemma card_Ohat_quot_span : .card (_ ⧸ span {(a : Ô E)}) = (span {a}).absNorm :=
  (card_eq_of_bijective _ (bijective_quot_Ô h (ext (by simp_all [↓dvd_iff_Ô])) (by simp))).symm

/-- For a nonzero integer a of the CM field E, the index of the principal level K(a) in K₀
(`Subgroup.relIndex`, 0 if infinite) is at most N(a)^(n²), with N(a) the absolute norm of
(a) and n the rank. -/
lemma relIndex_principalLevel_le [IsCMField E] : (principalLevel n a).relIndex (Kf ..) ≤
  absNorm (span {a}) ^ Fintype.card
  n ^ 2 := have := finite_of_card_ne_zero ((card_Ohat_quot_span h).trans_ne (by simpa))
  by grw [← card_Ohat_quot_span h, ← card_GL_le, ← (map n (mk _)).range.card_le_card_group,
       ← index_ker]
     exact index_antitone fun _ ↦ by simpa [↓eq_zero_iff_dvd] using! id
