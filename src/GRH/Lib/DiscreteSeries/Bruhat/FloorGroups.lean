import GRH.Lib.Adelic.Witt.FrameAction
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar measure
(known result; see Lib.DiscreteSeries.Bruhat.ComplexPlace).

This file: Flag stabilisers, unipotent radicals, Levi factors and Weyl-torus elements of a unitary
group. -/

noncomputable section


open Matrix FI Sum Subgroup Ring Fintype
variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {T : 𝔰.Form A} (l : ℕ) {a : Fin 𝔰.ϱ}

/-- The floor of a basis index: a for e_{a+1} and e*_{a+1}, ϱ for z, and ϱ+1 for the basis
vectors of X₀. -/
def floorOf : 𝔰.BesselIndex → ℕ | inl a | eStar a => a | inr (inl (inl _)) => 𝔰.n | _ => 𝔰.ϱ

/-- The involution of the basis indices that exchanges e_a and e*_a and fixes the indices of the
middle block. -/
def oppositeIndex : 𝔰.BesselIndex → 𝔰.BesselIndex | inl a => eStar a | eStar a => inl a | i => i

attribute [simp] floorOf.eq_1 floorOf.eq_2 floorOf.eq_3 floorOf.eq_4 oppositeIndex.eq_1
  oppositeIndex.eq_2 oppositeIndex.eq_3

/-- For b ≤ ϱ and an isometry g, the vector g⁻¹f_{b+1}, where f = (e₁, …, e_ϱ, z) is the frame. -/
def orbitPoint b (g : T.G) := g⁻¹.1.1 *ᵥ Pi.single (𝔰.besselFrame b) 1

@[grind .] lemma floorOf_level_cases : ∀ i : 𝔰.BesselIndex, (floorOf i = level i ∨
  level i + floorOf i = 2 * 𝔰.ϱ) ∧ floorOf i < 𝔰.ϱ ∨
  level i = 𝔰.ϱ ∧ 𝔰.ϱ ≤ floorOf i ∧ floorOf i ≤ 𝔰.n := by simp [level]; lia

attribute [-simp] Fintype.sum_sum_type

lemma oppositeIndex_spec : ∀ i : 𝔰.BesselIndex, oppositeIndex (oppositeIndex i) = i ∧
  floorOf (oppositeIndex i) = floorOf i ∧ level (oppositeIndex i) + level i = 2 * 𝔰.ϱ :=
  by simp [level]; lia

omit [StarRing A] in
@[simp] lemma splitGram_eq_ite_oppositeIndex : ∀ i j, floorOf i < 𝔰.ϱ ∨ floorOf j < 𝔰.ϱ →
  T.splitGram i j = ite (oppositeIndex i = j) 1 0 := by simp [splitGram]

/-- The isometry e ↦ ce*, e* ↦ e/c̄, c = p(a), on the hyperbolic pair of each floor a < ϱ
satisfying P with p(a) a unit; it fixes the other basis vectors. -/
def weylOn (P : ℕ → Prop) (p : ℕ → A) :
  T.G := let M (p : ℕ → A) := of fun i j ↦ let s := P (floorOf j) ∧ floorOf j < 𝔰.ϱ ∧ IsUnit (p
      (floorOf j)); ite (i = ite s (oppositeIndex j) j) (ite s (ite (level j <
      𝔰.ϱ) (p (floorOf j)) (star (p (floorOf j)))⁻¹ʳ) 1) 0; by use ⟨M p,
    M (star p), ?_, ?_⟩ <;> ext <;> simp [M, mul_apply, apply_ite star,
    inverse_star] <;> grind [splitGram_eq_ite_oppositeIndex, oppositeIndex_spec, inverse_mul_cancel]

/-- The Weyl element w_p of length l: e_a ↦ p_a e*_a and e*_a ↦ e_a/p̄_a on the first l
hyperbolic pairs, fixing the other basis vectors. -/
def weylElem (p : ℕ → Aˣ) : T.G := weylOn (· < l) (p ·)

/-- The Weyl element w_l(c): e_{l+1} ↦ ce*_{l+1}, e*_{l+1} ↦ e_{l+1}/c̄, fixing the other basis
vectors; it is 1 if l ≥ ϱ or c is not a unit. -/
def floorWeyl c := (weylOn (· = l) fun _ ↦ c : T.G)

@[simp ↓] lemma inverse_star_unit (u : Aˣ) : (star ↑u)⁻¹ʳ = star u⁻¹.1 := by aesop

attribute [local simp] weylOn weylElem floorWeyl level frameGram Matrix.mul_apply funext_iff

/-- The subgroup H_l of the unitary group fixing e_a and e*_a for a ≤ l; also z if l > ϱ, and
every basis vector if l > ϱ + 1. -/
def Shape.Form.GT := (agreeWithOneOn (fun _ j ↦ floorOf j < l) A).subgroupOf T.G

/-- The subgroup 𝒩_{<l} of the unitary group: block upper triangular with identity diagonal
blocks for e₁, …, e_l, V_l, e*_l, …, e*₁; for l ≥ ϱ it is 𝖴. -/
def Shape.Form.unipotentBelow :=
  (unitriangular (fun i ↦ ite (floorOf i < l) (level i) 𝔰.ϱ) A).subgroupOf T.G

/-- The group 𝒩_l = H_l ∩ 𝒩_{<l+1}, where H_l = U(V_l). -/
def floorUnipotent := T.GT l ⊓ T.unipotentBelow (l + 1)

/-- The subgroup Q_l of the unitary group: for l ≤ ϱ + 1, elements unitriangular on the first l
vectors of the frame (e₁, …, e_ϱ, z); otherwise 𝖴. -/
def Shape.Form.unitriGroup := (agreeWithOneOn (fun i j ↦ level j ≤ level i ∧
  (floorOf j ⊔ level j < l ∨ 𝔰.n < l)) A).subgroupOf T.G

export Shape.Form (GT unipotentBelow unitriGroup)

variable {l} {g s σ τ : T.G} {b : Fin 𝔰.n} {e v : 𝔰.BesselIndex → A} {P : ℕ → Prop} {p : ℕ → Aˣ}
  {j : ℕ}

lemma mem_floorGroup : g ∈ GT l ↔ ∀ i j, floorOf j < l → g.1 i j = (1 : Matrix ..) i j := .rfl

lemma floorGroup_apply (h : g ∈ GT l) i j (e : floorOf i < l ∧ floorOf i < 𝔰.ϱ ∨ floorOf j < l) :
  g.1 i j = (1 : Matrix ..)
  i j := e.elim (by simpa [mem_floorGroup.1 h, oppositeIndex_spec, ·,
  apply_ite] using congrFun₂ g.2 (oppositeIndex i) j) (h i j)

lemma mem_unipotentBelow : g ∈ unipotentBelow l ↔ ∀ i j, ite (floorOf j < l) (level j) 𝔰.ϱ ≤
  ite (floorOf i < l) (level i) 𝔰.ϱ → g.1 i j = (1 : Matrix ..) i j := .rfl

lemma mem_unitriGroup : g ∈ unitriGroup l ↔ ∀ i j, level j ≤ level i → floorOf j ⊔ level j < l ∨
  𝔰.n < l → g.1 i j = (1 : Matrix ..) i j := forall₂_congr (by simp)

lemma floorOf_besselFrame : floorOf (𝔰.besselFrame b) = b := b.lastCases (by simp) (by simp)

attribute [grind .] mem_floorGroup mem_unipotentBelow mem_unitriGroup floorOf_besselFrame
  level_besselFrame floorGroup_apply

attribute [local grind .] mem_besselU one_apply_ne mem_inf oppositeIndex_spec IsConcreteLE.le_iff
  floorUnipotent Antitone

lemma orbitPoint_eq_iff : orbitPoint b g = e ↔ g *ᵥ e = Pi.single (𝔰.besselFrame b) 1 :=
  inv_smul_eq_iff (g := g).trans comm

lemma mem_unitriGroup_succ_iff (h : s ∈ GT b) : s ∈ unitriGroup (b + 1) ↔ orbitPoint b s = Pi.single
  (𝔰.besselFrame b) 1 := by simp [↓orbitPoint_eq_iff, ← Matrix.one_apply]; grind [show ∀ j,
  floorOf j ⊔ level j = b → j = 𝔰.besselFrame b by cases b using Fin.lastCases <;> simp <;> lia]

lemma inv_mul_mem_of_orbitPoint_eq (h : σ ∈ GT b) (k : τ ∈ GT b) (e : orbitPoint b σ⁻¹ =
  orbitPoint b τ⁻¹) : σ⁻¹ * τ ∈ unitriGroup (b + 1) ⊓ GT
  b := by simpa [mem_unitriGroup_succ_iff, mul_mem, ↓orbitPoint_eq_iff, orbitPoint, *] using! e

@[simp] lemma mem_unitriGroup_of_mem_besselU : g ∈ besselU → g ∈ unitriGroup l := by grind

/-- For l ≥ ϱ, the block unitriangular group 𝒩_{<l} (`unipotentBelow`) equals the Bessel
unipotent group 𝖴. -/
lemma unipotentBelow_eq_besselU (h : 𝔰.ϱ ≤ l) : unipotentBelow l = T.besselU := by ext; grind

lemma unipotentBelow_le_besselU : unipotentBelow l ≤ T.besselU := by grind

lemma unipotentBelow_le_unitriGroup : T.unipotentBelow j ≤ unitriGroup l := by grind

lemma unitriGroup_anti : Antitone T.unitriGroup := by grind

lemma floorGroup_anti : Antitone T.GT := by grind

@[simp] lemma floorGroup_zero : T.GT 0 = ⊤ := by grind

lemma floorGroup_eq_bot (h : 𝔰.ϱ + 2 ≤ l) : T.GT l = ⊥ :=
  bot_unique fun _ _ ↦ by ext; push_cast; grind

/-- The top group Q_{ϱ+2} equals the Bessel unipotent group 𝖴. -/
@[simp] lemma unitriGroup_top_eq_besselU : unitriGroup (𝔰.ϱ + 2) = T.besselU := by ext; grind

lemma unitriGroup_inf_floorGroup_last : unitriGroup (𝔰.top + 1) ⊓ GT 𝔰.top =
  T.GT 𝔰.n := by ext; grind

@[simp] lemma mem_unitriGroup_of_mem_floorGroup : g ∈ GT l → g ∈ unitriGroup l := by grind

lemma eq_one_of_mem_floorGroup_inf (k : g ∈ GT l ⊓ unipotentBelow j) (h : j ≤ l ∨ 𝔰.ϱ ≤ l) :
  g = 1 := by ext;push_cast;grind

lemma floorUnipotent_superdiag_eq_zero (a : Fin _) : s ∈ floorUnipotent l → l ≠ a →
  s.1 (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ) = 0 := by grind

lemma conj_mem_unipotentBelow (h : σ ∈ GT l) : g ∈ unipotentBelow l →
  σ * g * σ⁻¹ ∈ unipotentBelow l := conj_mem_unitriangular (d := σ⁻¹.1) fun _ ↦ by grind [inv_mem h]

lemma conj_mem_floorUnipotent (h : g ∈ floorUnipotent l) σ (k : σ ∈ GT (l + 1)) :
  σ * g * σ⁻¹ ∈ floorUnipotent l :=
  by simp_all [floorUnipotent, conj_mem_unipotentBelow, mul_mem, floorGroup_anti l.le_succ k]

lemma superdiag_conj_eq (hn : g ∈ unipotentBelow l) (hs : s ∈ GT (l + 1)) :
    (s * g * s⁻¹).1 (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ) =
  g.1 (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.succ) := by
  by_cases a < l; simp [floorGroup_apply (l := l + 1), floorOf_besselFrame, le_of_lt, *, -coe_inv,
    -InvMemClass.coe_inv]; grind [conj_mem_unipotentBelow (floorGroup_anti l.le_succ hs) hn]

section

omit [StarRing A]

@[simp] lemma splitGram_col : ∀ i, floorOf i < 𝔰.ϱ → T.splitGram.col i =
  Pi.single (oppositeIndex i) 1 := by simp

@[simp] lemma splitGram_mulVec_pair : ∀ i, floorOf i < 𝔰.ϱ → (T.splitGram *ᵥ e) i =
  e (oppositeIndex i) ∧ (e ᵥ* T.splitGram) i = e (oppositeIndex i) :=
  by simp [splitGram, fromBlocks_mulVec, vecMul_fromBlocks]

lemma inclMatrix_val_mulVec u (i : 𝔰.BesselIndex) : (inclMatrix A Subtype.val *ᵥ u) i = if h : l ≤
  floorOf i then u ⟨i, h⟩ else 0 :=
  by split <;> simp [inclMatrix, mulVec_eq_sum, Subtype.coe_eq_iff, *]

end

lemma inclMatrix_mulVec_floor_block (hl : l ≤ 𝔰.ϱ) (h : s ∈ GT l) u : inclMatrix A (↑) *ᵥ
  s.1.1.toSquareBlockProp (l ≤ floorOf ·) *ᵥ u = s.1.1 *ᵥ inclMatrix A (↑) *ᵥ u := by
  simp [mul_inclMatrix, -funext_iff]; rcongr; apply
    (inclMatrix_val_mulVec ..).trans; simp [toSquareBlockProp]; grind

/-- For 0 ≤ b ≤ ϱ, σ in H_b and s in Q_{b+1}, the vector σf_{b+1} has coordinate zero at e_a and
e*_a for a ≤ b, and the coordinate of σs f_{b+1} at every other basis vector. -/
lemma floorGroup_apply_besselFrame (h : σ ∈ GT b) (k : s ∈ unitriGroup (b + 1)) i :
  σ.1 i (𝔰.besselFrame b) = ite (floorOf i < b) 0 ((σ * s).1 i (𝔰.besselFrame
  b)) := by split; grind; exact congrFun₂ (mul_one σ.1.1) .. ▸ sum_congr _ _ fun j ↦ by
                             by_cases floorOf j < b; simp [mem_floorGroup.1 h, *]; all_goals grind

@[simp] lemma floorWeyl_mem_floorGroup {c} : floorWeyl l c ∈ T.GT l := fun _ ↦ by simp; lia

lemma commute_weylOn {p} (h : ∀ a, P a → a < l) (hs : s ∈ GT l) : Commute (weylOn P p) s := by
  ext i; have := floorGroup_apply hs; simp [-Sum.forall] at *; rw [sum_eq_single
    (ite (P (floorOf i) ∧ floorOf i < 𝔰.ϱ ∧ IsUnit (p (floorOf i))) (oppositeIndex i) i)] <;> grind
    (splits := 20) only [oppositeIndex_spec]

@[simp] lemma weylElem_zero : (weylElem 0 p : T.G) = 1 := by aesop

lemma weylElem_succ : (weylElem (l + 1) p : T.G) =
  floorWeyl l (p l).1 * weylElem l p := by ext; simp; grind

@[simp] lemma weylElem_update c : (weylElem l (Function.update p l c) : T.G) =
  weylElem l p := by ext; simp; grind

lemma commute_weylElem : s ∈ GT l → Commute (weylElem l p) s := commute_weylOn (by lia)

@[simp] lemma weylElem_star : (weylElem l (star p) : T.G) = (weylElem l p)⁻¹ := by ext; rfl

lemma weylElem_mul_left_comm (h : s ∈ GT l) : weylElem l p * (s * g) = s * (weylElem l p * g) ∧
  (weylElem l p)⁻¹ * (s * g) =
  s * ((weylElem l p)⁻¹ * g) := by simp [← weylElem_star, (commute_weylElem h).left_comm, -weylElem]

/-- Let the form h with Gram matrix `T.splitGram` be hermitian and invertible. For isometries σ, τ
and 0 ≤ b ≤ ϱ, the diagonal entry of Z(στ⁻¹) at the frame vector f_{b+1} is h(σ⁻¹f_{b+1},
τ⁻¹f_{b+1}). -/
lemma frameGram_eq_form_orbitPoint : T.frameGram (σ * τ⁻¹).1 b b =
  star (orbitPoint b σ) ⬝ᵥ T.splitGram *ᵥ orbitPoint b τ := by
  rw [← U.form_mulVec_mulVec, orbitPoint_eq_iff.1 rfl, orbitPoint]; simp [↓mulVec_mulVec, mul_assoc]

lemma frameGram_floorWeyl (c : Aˣ) : T.frameGram (floorWeyl a c : T.G).1 a.castSucc a.castSucc =
  c := by simp

lemma level_le_or_exists_dual (k : 𝔰.BesselIndex) : level k ≤ 𝔰.ϱ ∨ ∃ b, k = eStar b ∧ floorOf k =
  b := by bound

lemma unipotentBelow_mulVec_apply (hν : g ∈ unipotentBelow j) (hv : ∀ b : Fin _, b < j →
  v (eStar b) = 0) i (hi : j ≤ floorOf i ∨ 𝔰.ϱ < level i) : (g *ᵥ v) i =
  v i := congr($(one_mulVec v) i) ▸ sum_congr _ _ (by grind [level_le_or_exists_dual ·])

/-- For s in Q_j and a < j (hyperbolic pairs indexed from 0), the row of s at e*_a equals that
of the identity matrix in every column other than those of the e*_b with b < a. -/
lemma unitriGroup_dual_row (hs : s ∈ unitriGroup j) (ha : a < j) k : (∀ b < a, k ≠ eStar b) →
    s.1 (eStar a) k = (1 : Matrix 𝔰.BesselIndex ..) (eStar a) k := by
  obtain _ := (mem_unitriGroup.1 (inv_mem hs) · (inl a)), congr($(U.form_mul_inv_eq s⁻¹) (inl a))
  simp_all [sum_sum_type]; grind [star_zero, star_one]

lemma unitriGroup_mulVec_dual (hs : s ∈ unitriGroup j) (ha : a < j) (h : ∀ b < a, v (eStar b) = 0) :
  (s.1.1 *ᵥ v) (eStar a) =
  v (eStar a) := congr($(one_mulVec v) _) ▸ sum_congr _ _ (by grind [unitriGroup_dual_row])
