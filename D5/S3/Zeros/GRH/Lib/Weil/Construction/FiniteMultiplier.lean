/- GID: D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteMultiplier
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Construction/FiniteMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Construction.FiniteMultiplier. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Construction/FiniteMultiplier.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Weil.Unramified.HeckeGL
import D5.S3.Zeros.GRH.Lib.Adelic.Witt.SpaceOperations
import D5.S3.Zeros.GRH.Lib.Weil.Construction.FiniteVacuum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Finite multiplier of the splitting through saturating matrices; multiplicativity, phase,
lattice index. -/

noncomputable section


section

variable {E ι κ B B' : Type*} [Ring B] [Ring B'] (S : Subring B) (g u : Bˣ)

/-- For a subring S and units g, u of a ring: u and gu lie in S and lu + m·gu = 1 for some l, m
in S. For matrices this says uΛ = Λ ∩ g⁻¹Λ. -/
def Sat := ↑u ∈ S ∧ g.1 * u ∈ S ∧ ∃ l ∈ S, ∃ m ∈ S, u⁻¹ = l + m * g

variable {S g u}
attribute [local simp] Sat add_mul mul_assoc Circle.norm_coe RingHom.map_det IsConcreteLE.le_iff

lemma Sat.inv_mul_mem x p : Sat S g u → x ∈ S ∧ g * x ∈ S ∧ p → u⁻¹ * x ∈ S := by aesop

lemma Sat.map_of_le_comap (h : Sat S g u) (f : B →+* B') {S'} : S ≤ .comap f S' → Sat S' (g.map f)
    (u.map f) := by simp_all; grind

lemma Sat.of_mem : ↑g ∈ S → Sat S g 1 := by aesop

open MeasureTheory Matrix ComplexConjugate NumberField GeneralLinearGroup WeilData stdLattice Valued
  Sat
variable [Field E] [NumberField E] [Fintype ι] [Fintype κ] {g u b b' k k' : GL ι (𝔸f E)} (w :
  FinPlace E)

@[local simp] lemma mem_subring_matrix_iff {x} : x ∈ S.matrix ↔ ∀ i j : ι, x i j ∈ S := .rfl

lemma ideleAbs_locFullIdele x : ideleAbs (locFullIdele w x) = ‖x.1‖ := finIdeleAbs_locIdele x

variable {w} (g)

/-- Every invertible matrix g over the finite adeles has an invertible u related to it by
`Sat` over integral matrices, the relation expressing uÔ^ι = Ô^ι ∩ g⁻¹Ô^ι. -/
lemma Sat.exists_saturating : ∃ u, Sat (Ô E).matrix g u :=
  (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul (X := (diagonal 1).fromRows
  g.1) ⟨fromCols 1 0, by simp⟩).imp fun u ⟨_, _, L, _⟩ ↦ by use ?_, ?_, L.toCols₁, ?_, L.toCols₂,
  ?_, (u.inv_eq_of_mul_eq_one_left ?_) <;> simp_all [IsIntMatrix, ← fromCols_mul_fromRows]

/-- For g in GL_ι(𝔸_f), a chosen u in GL_ι(𝔸_f) with u and gu integral and u⁻¹ = l + mg for some
integral matrices l, m (`Sat`). -/
def saturatingElem := (nonempty_subtype.2 (Sat.exists_saturating g)).some

lemma Sat.map_evalAt (h : Sat (Ô E).matrix b u) w : Sat (LocInt w).matrix (b.map (evalAt w))
    (u.map (evalAt w)) := h.map_of_le_comap (evalAt w).mapMatrix (by simp_intro _ _ [Ô])

end

attribute [local simp] Sat add_mul mul_assoc Circle.norm_coe RingHom.map_det IsConcreteLE.le_iff

open MeasureTheory Matrix ComplexConjugate NumberField GeneralLinearGroup WeilData stdLattice Valued
  Sat

attribute [local simp] mem_subring_matrix_iff

variable {E ι κ B : Type*} [Ring B] {S : Subring B} [Field E] [CMType E] [Fintype ι] [Fintype κ]
  (g : GL ι (𝔸f E)) {u b b' k k' : GL ι (𝔸f E)} {w : FinPlace E} [WeilData E]

/-- The homomorphism x ↦ υ(x)|x|^(−1/2) from the ideles of E to ℂ, with υ the splitting
character and |x| the idele norm. -/
@[local simp] def chiAdelic : (𝔸 E)ˣ →* ℂ :=
  ⟨⟨fun x ↦ υ.1 x * (↑√(ideleAbs x))⁻¹, by simp⟩, by simp [field]⟩

/-- The character x ↦ υ(x)|x|^(−1/2) of the finite ideles of E, x being extended by 1 at
infinity. -/
def chiFin := chiAdelic (E := E).comp finIdeleIncl

lemma chiFin_congr {x y : (𝔸f E)ˣ} (h : ∀ w, v (x.1 w) = v (y.1 w)) : chiFin x = chiFin y := by
  simp_all [chiFin, upsilon_eq_prod_mul_of_v_eq y, ideleAbs, FinitePlace.norm_def]

/-- For g in GL_n(𝔸_f), Δ_f(g) = υ(det λ)|det λ|^(−1/2), λ a chosen invertible matrix with λ, gλ
integral and lλ + m·gλ = 1, l, m integral. -/
def glMultiplier := chiFin (det (saturatingElem g).1)

omit [WeilData E] in
/-- Let u be the matrix chosen by `Sat.exists_saturating` with uÔⁿ = Ôⁿ ∩ b⁻¹Ôⁿ. If y satisfies
`Sat` over O_w for the component of b at w, then det u at w and det y have the same
valuation. -/
lemma Sat.v_det_saturatingElem {x y} (e : b.map (evalAt w) = x) (h : Sat (LocInt w).matrix x y) :
    v ((saturatingElem b).1.1.det w) = v y.1.det := have s := e ▸ (saturatingElem b).2.map_evalAt w
             eq_of_inv_mul_eq_one (by simpa [← evalAt_apply] using (mem_intGL_iff_det.1
               (mem_intGL (g := _ * _).2 ⟨s.inv_mul_mem _ _ h, h.inv_mul_mem _ _ s⟩)).2)

/-- Let b, u be in GL_n(𝔸_f) with u and bu integral and lu + mbu = 1 for some integral matrices
l, m. Then Δ_f(b) = χ_f(det u). -/
lemma Sat.glMultiplier_eq (h : Sat (Ô E).matrix b u) : glMultiplier b = chiFin u.det :=
  chiFin_congr (by simpa [← evalAt_apply] using (h.map_evalAt · |>.v_det_saturatingElem rfl))

/-- For an invertible matrix g over the finite adeles, Δ_f(g⁻¹) = υ(det g)|det g|^(−1/2) Δ_f(g). -/
lemma glMultiplier_inv : glMultiplier g⁻¹ = chiFin g.det * glMultiplier g := by
  erw [← map_mul, ← map_mul, glMultiplier_eq]
  simp [-mem_subring_matrix_iff, -coe_units_inv, Units.mul_inv_eq_iff_eq_mul]; grind [Sat]

lemma glMultiplier_mul_of_mem (h : k ∈ intGL ι (Ô E)) (_ : k' ∈ intGL ι (Ô E)) :
  glMultiplier (k * g * k') = glMultiplier g := by
  obtain ⟨⟨_, _, l, _, m, _⟩, _⟩ := (saturatingElem g).2, glMultiplier_inv k'⁻¹
  rw [glMultiplier_eq (u := k'⁻¹ * _) ⟨_, _, l * k'.1, _, m * k⁻¹, _⟩]
  repeat simp_all [mem_intGL, glMultiplier_eq ∘ .of_mem, mul_mem] <;> rfl

lemma Sat.glMultiplier_transpose (h : Sat (Ô E).matrix b u) (e : b'.1 = bᵀ) : glMultiplier b' =
  chiFin u.det := by grind [exists_invTransposeGL_inv_eq isValuationPair_Ohat b, Units.ext (v :=
  invTransposeGL b⁻¹) e, glMultiplier_mul_of_mem, invTransposeGL_mem_intGL, glMultiplier_eq]

/-- If b' is the conjugate transpose of the invertible finite adelic matrix b, then Δ_f(b') is
the complex conjugate of Δ_f(b). -/
lemma glMultiplier_star : glMultiplier (star b) = conj (glMultiplier b) := by
  erw [glMultiplier_transpose ((saturatingElem b).2.map_of_le_comap (conj).mapMatrix _),
    congrArg chiAdelic (_ : _ = star _)] <;> aesop (add simp [glMultiplier, chiFin, υ_star,
    Complex.inv_eq_conj, det_apply', star_mem_Ô, (@starRingEnd_apply (𝔸f E))])

/-- If b, b′ in GL_n(𝔸_f) are such that at every finite place at least one of them has component
1, then Δ_f(bb′) = Δ_f(b)Δ_f(b′). -/
lemma glMultiplier_mul (h : ∀ w, b.map (evalAt w) = 1 ∨ b'.map (evalAt w) = 1) :
  glMultiplier (b * b') = glMultiplier b * glMultiplier b' :=
  (chiFin_congr (by cases h · <;> simp [*, v_det_saturatingElem _ ∘ .of_mem,
  ((saturatingElem (b * b')).2.map_evalAt _).v_det_saturatingElem])).trans (map_mul ..)

/-- Δ_f is multiplicative on blocks: if an invertible finite adelic matrix G is, after
reindexing by a bijection e, block diagonal with invertible blocks g and g′, then Δ_f(G) =
Δ_f(g)Δ_f(g′). -/
lemma glMultiplier_fromBlocks g' {n} [Fintype n] (e : n ≃ ι ⊕ κ) {G} (h : G.1 =
  (fromBlocks g.1 0 0 g'.1).submatrix e e) : glMultiplier G = glMultiplier g * glMultiplier g' := by
  obtain ⟨⟨_, _, _, _, c, _⟩, _, _, _, _, d, _⟩ := (saturatingElem g).2, (saturatingElem g').2
  erw [glMultiplier_eq (u := reindexGL e.symm (blockGL (_, _))) ⟨_, _, _, _, (c.fromBlocks 0 0
    d).submatrix e e, _, eq_add_of_sub_eq rfl⟩, ← map_mul]; congr with
  repeat simp_all [reindex_equiv e.symm, inv_fromBlocks_zero₂₁_of_isUnit_iff'] <;> rfl

/-- For b, b′ in GL_ι(𝔸_f) with b′ the conjugate transpose of b⁻¹, one has Δ_f(b′)Δ_f(b) =
|Δ_f(b)|² · conj χ_f(det b), where χ_f = υ|·|^(−1/2). -/
lemma glMultiplier_star_inv_mul : glMultiplier (star b⁻¹) * glMultiplier b = ‖glMultiplier
  b‖ ^ 2 * conj (chiFin b.det) := by grind [glMultiplier_star, glMultiplier_inv, Complex.conj_mul']

/-- Let b in GL_ι(𝔸_f) be 1 away from w, and y invertible over E_w with y, b_w y integral and ly
+ m b_w y = 1, l, m integral. Then Δ_f(b) = (υ(ϖ_w)√q_w)^{ord_w det y}, ϖ_w the chosen
uniformiser. -/
lemma glMultiplier_eq_pow_of_local {y} (h : ∀ x ≠ w, b.map (evalAt x) = 1) (s :
  Sat (LocInt w).matrix (b.map (evalAt w)) y) :
  glMultiplier b = (υ.atUnif w * √w.q) ^ (-(v y.1.det).log).toNat := by
  erw [glMultiplier, chiFin_congr, (chiAdelic.comp (locFullIdele w)).map_pow (uniformizer w)]
  repeat simp +contextual [← and_forall_ne w, h, s.v_det_saturatingElem, det_ne_zero,
    v_det_saturatingElem _ ∘ .of_mem, norm_locField_eq_q_zpow, ideleAbs_locFullIdele,
    WithZero.log_le_iff_le_exp, (v.mem_integer_iff _).1 (IsIntMatrix.det_mem s.1)] <;> rfl

/-- For g in GL_ι(𝔸_f), the set of x in Ô^ι with gx in Ô^ι has volume |Δ_f(g)|⁻², for the Haar
measure giving Ô^ι mass one. -/
lemma latticeMeasure_inter_eq_glMultiplier : (latticeMeasure E ι).real
  {x | g *ᵥ x ∈ stdLattice E ι ∧ x ∈ stdLattice E ι} = (‖glMultiplier g‖ ^ 2)⁻¹ := by
  rw [Measure.real, @Set.ext _ {x | _} ((saturatingElem g).1⁻¹.1.mulVec ⁻¹' stdLattice E ι) fun x ↦
    ⟨fun e i ↦ (saturatingElem g).2.inv_mul_mem (replicateCol ι x) True (by aesop) i i, fun e ↦ by
    simpa using! (saturatingElem g).2.symm.imp (IsIntMatrix.mulVec ·.1 e) (IsIntMatrix.mulVec · e)⟩,
    ← Measure.map_apply
    (by fun_prop) isOpen_stdLattice.measurableSet, map_mulVec_haar_finAdele, glMultiplier]
  simp [chiFin, finIdeleAbs]

variable (g : Gf E ι)

/-- For g in the finite adelic unitary group, the number Δ_f(g) = `glMultiplier` of its underlying
invertible matrix. -/
def finMultiplier := glMultiplier g.1

/-- For g in the finite adelic unitary group G_f, Δ_f(g⁻¹) is the complex conjugate of Δ_f(g). -/
lemma finMultiplier_inv : finMultiplier g⁻¹ = conj (finMultiplier g) :=
  .trans congr(glMultiplier $(Units.ext (U.inv_val_eq_conjTranspose g))) glMultiplier_star

lemma finMultiplier_eq_one_of_mem {k} : k ∈ Kf E ι →
  finMultiplier k = 1 := by simp_all [mem_Kf, finMultiplier, glMultiplier_eq ∘ .of_mem]

lemma finMultiplier_ne_zero : finMultiplier g ≠ 0 := (chiFin.toHomUnits _).ne_zero

/-- For g in the finite adelic unitary group, |Δ_f(g)|² equals the index of Ô^ι ∩ g⁻¹Ô^ι in Ô^ι. -/
lemma norm_finMultiplier_sq : ‖finMultiplier g‖ ^ 2 =
  ((stdLattice E ι).comap g.1.1.mulVecLin).relIndex (stdLattice E ι) :=
  inv_injective (flip .trans ((congrArg _ (measure_inter_eq_inv_relIndex_add isCompact_stdLattice
  (isOpen_stdLattice.preimage_of_continuous (f := (g • ·))) _ latticeMeasure_stdLattice)).trans
  (ENNReal.toReal_inv _)) (latticeMeasure_inter_eq_glMultiplier _).symm)

/-- For g in G_f, υ(det g)·Δ_f(g) is the complex conjugate of Δ_f(g), where det g is read as an
idele with component 1 at the infinite places. -/
lemma upsilon_mul_finMultiplier : υ.1 (finIdeleIncl g.1.det) * finMultiplier g = conj
  (finMultiplier g) := .symm (finMultiplier_inv g ▸ by simpa [finMultiplier, glMultiplier_inv,
  chiFin, mul_left_eq_self₀, abs_of_nonneg] using congr(‖$(finMultiplier_inv g)‖))

/-- Let S be a set of finite places disjoint from S̄, and g in G_f supported on S ∪ S̄. If a
equals g above S and 1 elsewhere, then Δ_f(g) = |Δ_f(a)|² · conj χ_f(det a). -/
lemma finMultiplier_eq_of_supportedOn {S} (hS : S.IsConjDisjoint) {g : Gf E ι} (hg :
  g ∈ Gf.supportedOn ι S) : let a := cutGL (idem_mul_self S) g.1; finMultiplier g = ‖glMultiplier
    a‖ ^ 2 * conj (chiFin a.det) := by rw [finMultiplier, congrArg glMultiplier (GL_ext_evalAt _),
  glMultiplier_mul, glMultiplier_star_inv_mul] <;> intro w <;> by_cases w ∈ S <;> by_cases star w ∈
  S <;> simp_all [Gf.atPlace, map_evalAt_cutGL, -coe_units_inv, Units.ext_iff,
  evalAt_star_GL (star_star _), -star_inv, Set.disjoint_left]; apply g.atPlace_star
