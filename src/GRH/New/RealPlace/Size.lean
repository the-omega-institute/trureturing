import GRH.Lib.DiscreteSeries.Bruhat.FloorGroups
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Size filtrations; size bounds for minors, heads and group elements near two frames.
Q_j is `Shape.Form.unitriGroup`, 𝒩_{<j} is `Shape.Form.unipotentBelow`, w_p is `weylElem`. -/


open Matrix FI Sum Fintype MatMul Finset Fin
variable {A l n : Type} [CommRing A] [StarRing A] {𝔰 : Shape} (T : 𝔰.Form A) {α β}

/-- A size: sets B_i ∋ 0, 1 of A, stable under − and involution, B_iB_j ⊂ B_{i+j}, sums of ≤
rank+1 terms of B_i in B_{i+1}, Gram matrix and inverse in B₁. -/
structure Size where
  ofSize : ℕ → Set A
  mul_mem_ofSize {i j x y} : x ∈ ofSize i → y ∈ ofSize j → x * y ∈ ofSize (i + j)
  sum_mem_ofSize {i} {n : Type} [Fintype n] {f : n → A} :
    card n ≤ 𝔰.r + 1 → (∀ a, f a ∈ ofSize i) → ∑ a, f a ∈ ofSize (i + 1)
  neg_star_mem_ofSize {i x} : (-x ∈ ofSize i ↔ x ∈ ofSize i) ∧ (star x ∈ ofSize i ↔ x ∈ ofSize i)
  zero_one_mem_ofSize i : 0 ∈ ofSize i ∧ 1 ∈ ofSize i
  gram_mem_ofSize : (∀ i j, T.splitGram i j ∈ ofSize 1) ∧ ∀ i j, T.splitGram⁻¹ i j ∈ ofSize 1

variable {T} {c d i j} {s g x u : T.G} {v w : 𝔰.BesselIndex → A} {a :
  Fin 𝔰.ϱ} {p q} {r : Aˣ} {S : Size T} {X Z : Matrix l 𝔰.BesselIndex A}

/-- The element w_q⁻¹w_p of the unitary group of V over A, for the Weyl elements w_p, w_q of
length j. -/
noncomputable def weylRatio j p q := (weylElem j q)⁻¹ * (weylElem j p : T.G)

lemma coe_weylRatio : (weylRatio j p q : T.G).1.1 = diagonal fun i ↦ ite (floorOf i < j ⊓ 𝔰.ϱ) (ite
    (level i < 𝔰.ϱ) (p (floorOf i) / q (floorOf i)).1 (star (q (floorOf i) / p (floorOf i)).1))
  1 := by ext; simp [weylRatio, weylElem, mul_apply, diagonal, weylOn,
  division_def]; grind [oppositeIndex_spec]

lemma weylRatio_inv : (weylRatio j p q : T.G)⁻¹ = weylRatio j q p := rfl

/-- For a < ϱ, the number of basis indices of floor (`floorOf`) at least a + 1 is k + 1
+ 2(ϱ − (a + 1)), the rank of the orthogonal complement of the first a + 1 hyperbolic
planes. -/
lemma card_succ_le_floorOf : card {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} = 𝔰.k + 1 + 2 *
  (𝔰.ϱ - (a + 1)) := by simp [card_congr .subtypeSum, Fintype.card_subtype, filter_lt_eq_Ioi]; lia

namespace Size

/-- The vector v has size i: all its entries lie in B_i. -/
def vecsOfSize i := {v : n → A | ∀ a, v a ∈ S.ofSize i}

/-- The matrix X has size i: all its entries lie in B_i. -/
def HasMatSize i (X : Matrix l n A) := ∀ a b, X a b ∈ S.ofSize i

/-- The units p form a head of length j for the size S: the inverse of every product D_l =
p₁⋯p_l, l ≤ j, has size 1. -/
def IsHead j (p : ℕ → Aˣ) := ∀ l ≤ j, (∏ a ∈ .range l, p a)⁻¹.1 ∈ S.ofSize 1

attribute [local simp] mul_sub zero_one_mem_ofSize neg_star_mem_ofSize level ite_mem ne_of_gt weylOn
  weylElem HasMatSize val_lt_of_le

lemma IsHead.star_head : S.IsHead j p → S.IsHead j (star p) := by simp [IsHead, ← star_prod]

lemma mem_ofSize_mono (h : α ∈ S.ofSize i) (e : i ≤ j := by lia) :
  α ∈ S.ofSize j := by grind [S.mul_mem_ofSize h (S.zero_one_mem_ofSize (j - i)).2]

lemma sub_mem_ofSize : α ∈ S.ofSize i → β ∈ S.ofSize i → α - β ∈ S.ofSize (i + 1) := by
  simpa [sub_eq_add_neg] using S.sum_mem_ofSize (f := ![α, -β]) (by simp +arith)

lemma HasMatSize.mono (h : S.HasMatSize i X) (e : i ≤ j := by lia) : S.HasMatSize j X :=
  (S.mem_ofSize_mono <| h · ·)

lemma HasMatSize.one : S.HasMatSize i (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) := by simp

lemma HasMatSize.sub : S.HasMatSize i X → S.HasMatSize i Z →
  S.HasMatSize (i + 1) (X - Z) := by simp_all [sub_mem_ofSize]

lemma dotProduct_mem_ofSize (h : ∀ a, v a ≠ 0 → w a ∈ S.ofSize i) (k : v ∈ S.vecsOfSize j) :
  w ⬝ᵥ v ∈ S.ofSize (i + j + 1) :=
  S.sum_mem_ofSize le_self_add (by grind [mul_mem_ofSize, zero_one_mem_ofSize, vecsOfSize])

lemma HasMatSize.mulVec : S.HasMatSize i X → v ∈ S.vecsOfSize j →
  X *ᵥ v ∈ S.vecsOfSize (i + j + 1) := fun h k _ ↦ dotProduct_mem_ofSize (by tauto) k

lemma HasMatSize.mul {Y : Matrix 𝔰.BesselIndex n A} : S.HasMatSize i X → S.HasMatSize j Y →
  S.HasMatSize (i + j + 1) (X * Y) := fun h k _ b ↦ h.mulVec (k · b) _

lemma det_mem_ofSize : ∀ Z : Matrix (Fin j) _ A, j ≤ 𝔰.ϱ → S.HasMatSize 7 Z →
  Z.det ∈ S.ofSize (8 * j) := j.rec (by simp) fun _ k Z _ h ↦
  det_succ_row_zero' Z ▸ mem_ofSize_mono (S.sum_mem_ofSize (by simp; lia) fun _ ↦
  S.mul_mem_ofSize (i := 7) (by simp_all [neg_one_pow_eq_ite]) (k _ (by lia) (by tauto)))

/-- Let JX = YᴴJ, J the Gram matrix of V. If every row n of Y with J_{nb} ≠ 0 has size i, then
the entry X_{ab} has size i + 4. -/
lemma adjoint_apply_mem_ofSize [IsHermUnit T.splitGram]
    {X Y} (e : T.splitGram * X = Yᴴ * T.splitGram) a b (h : ∀ n,
  T.splitGram n b ≠ 0 → Y n ∈ S.vecsOfSize i) : X a b ∈ S.ofSize (i + 4) :=
  nonsing_inv_mul_cancel_left _ X (‹IsHermUnit _›.2.map detMonoidHom) ▸ e ▸ mem_ofSize_mono
  (HasMatSize.mulVec S.gram_mem_ofSize.2 (fun m ↦
  dotProduct_mem_ofSize (by simpa using h · · m) (S.gram_mem_ofSize.1 · b)) a)

lemma HasMatSize.inv [IsHermUnit T.splitGram]
    (h : S.HasMatSize i x.1.1) : S.HasMatSize (i + 4) x⁻¹.1.1 :=
  (adjoint_apply_mem_ofSize (U.form_mul_inv_eq _) · · (by tauto))

lemma row_mem_ofSize_of_dual_frame m (h : ∀ a, a.1 < j → ∃ w,
  (∀ b ≤ a, w (eStar b) = ite (b = a) 1 0) ∧ w ∈ S.vecsOfSize c ∧ X *ᵥ w ∈ S.vecsOfSize d) (z : ∀ k,
  j ≤ floorOf k ∨ level k ≤ 𝔰.ϱ → X m k ∈ S.ofSize d) i : ∀ k, j ≤ floorOf k + i ∨ level k ≤ 𝔰.ϱ →
  X m k ∈ S.ofSize (d + (c + 3) * i) := i.rec z fun i ih k l ↦ by_cases (mem_ofSize_mono <|
  ih k ·) fun _ ↦ (h ⟨floorOf k, by grind⟩ (by lia)).rec fun w ⟨_, hw, e⟩ ↦ mem_ofSize_mono
  (by simpa [entrywise] using sub_mem_ofSize (mem_ofSize_mono (e m)) (dotProduct_mem_ofSize
  (fun k l ↦ ih k (by grind [level_le_or_exists_dual, Matrix.one_apply, -Sum])) fun l ↦
  sub_mem_ofSize (hw l) (HasMatSize.one l k)))

/-- Back substitution. Let u ∈ 𝒩_{<j} and r = r̄ be a unit of size 1. If for each a ≤ min(j, ϱ)
some w ∈ e*_a + ⟨e₁, …, e_a⟩^⊥ has w and (w − uw)/r of size c, then (1 − u⁻¹)/r has size c +
4 + (2c + 8)j. -/
lemma hasMatSize_one_sub_inv [IsHermUnit T.splitGram]
    (hu : u ∈ unipotentBelow j) (hr : star r.1 = r ∧ ↑r ∈ S.ofSize 1) (h :
  ∀ a : Fin 𝔰.ϱ, a.1 < j → ∃ w, (∀ b ≤ a, w (eStar b) = ite (b = a) 1 0) ∧ w ∈ S.vecsOfSize c ∧
  (r⁻¹.1 • (1 - u.1.1)) *ᵥ w ∈ S.vecsOfSize c) : S.HasMatSize (c + 4 + (2 * c + 8) * j) (r⁻¹.1 •
  (1 - u⁻¹.1.1)) := fun i k ↦ mem_ofSize_mono (row_mem_ofSize_of_dual_frame i (h · · |>.elim
  fun w ⟨e, m, n⟩ ↦ ⟨u *ᵥ w, by grind [unitriGroup_mulVec_dual (unipotentBelow_le_unitriGroup hu)
  .refl], fun k ↦ by simpa using (sub_mem_ofSize (mem_ofSize_mono (m k)) (S.2 hr.2 (n k))),
  (mem_ofSize_mono <| by simpa using S.4.1.2 <| n ·)⟩) (fun k e ↦ adjoint_apply_mem_ofSize
  (by simp [*, ← inverse_star_unit, ← U.form_mul_inv_eq]) i k fun n l ↦
  (row_mem_ofSize_of_dual_frame n h (fun m _ ↦ by simp [mem_unipotentBelow.1 hu n m (by grind
  [splitGram_eq_ite_oppositeIndex, oppositeIndex_spec, -Sum])]) j · (by lia))) j k (by lia))

variable {K : Set (U _)} (o : ∀ ⦃x⦄, x ∈ K → S.HasMatSize 1 x.1.1) (hj : j ≤ 𝔰.ϱ)
  (h' : ∃ η ∈ unitriGroup j, η * ((weylElem j p)⁻¹ * g) ∈ K) (h : s ∈ unitriGroup j ∧ s * g ∈ K)
include o hj h' h

/-- Let K consist of elements of size 1, j ≤ ϱ, s ∈ Q_j, sg ∈ K, and let Q_j w_p⁻¹g meet K. For
a ≤ j, every entry of the column D_a·s e*_a, D_a = p₁⋯p_a, has size 9(ϱ+1). -/
lemma minor_mul_dual_mem_ofSize [IsHermUnit T.splitGram]
    (ha : a < j) i : (∏ b ∈ .range (a + 1), p b).1 * s.1.1 i (eStar a) ∈
    S.ofSize (9 * 𝔰.n) := h'.rec fun η ⟨r, h'⟩ ↦ mem_ofSize_mono (by
  have y m d l := inv_mem r m (inl (.castLE a.2 d)) ⟨l, by simp [ha]⟩
  convert det_mem_ofSize _ a.2 fun b d ↦ (o h.2).mul (o h').inv (ite (b = .last _) i
    (eStar (b.castLE a.2))) (inl (d.castLE a.2))
  simp [-coe_units_inv]
  erw [← mul_assoc, det_eq_of_eq_mul_det_one _ (det_eq_one_of_unitriangular fun _ ↦
    (y _ · · |>.trans (by simp))) (ext fun b d ↦ .symm (sum_of_injective _
    (inl_injective.comp (castLE_injective a.2)) _ _ (fun m _ ↦ by dsimp; erw [y] <;> revert m <;>
    simp [Fin.exists_iff] <;> grind) fun _ ↦ rfl)), det_of_isLowerTriangular _ fun b
    d ↦ by simp [mul_apply, *]; grind [unitriGroup_dual_row, one_apply_ne]]
  simp +contextual [prod_univ_castSucc, prod_range, unitriGroup_dual_row h.1, ha.le, mul_apply, *]
  ac_rfl)

/-- Let K consist of elements of size 1 and j ≤ ϱ. If sg ∈ K for an s in Q_j and Q_j w_p⁻¹g
meets K, then every product D_l = p₁⋯p_l, l ≤ j, has size 9(ϱ+1). -/
lemma minors_mem_ofSize [IsHermUnit T.splitGram] :
    ∀ l ≤ j, (∏ a ∈ .range l, p a).1 ∈ S.ofSize (9 * 𝔰.n) := by
  rintro (_ | l) e; simp; lift l to Fin 𝔰.ϱ using by lia
  simpa +contextual [unitriGroup_dual_row h.1 e] using
    minor_mul_dual_mem_ofSize o hj h' h e (eStar l)

/-- Let K consist of elements of size 1, j ≤ ϱ, s ∈ Q_j, sg ∈ K, and let Q_j w_p⁻¹g meet K. If p
is a head, then p_a, p_a⁻¹ and the column s e*_a, a ≤ j, have size 10(ϱ+1). -/
lemma head_entries_mem_ofSize [IsHermUnit T.splitGram]
    (hp : S.IsHead j p) (ha : a < j) : let N := S.ofSize (10 * 𝔰.n)
  (p a).1 ∈ N ∧ (p a)⁻¹.1 ∈ N ∧ ∀ i, s.1.1 i (eStar a) ∈ N := by
  obtain _ := S.mul_mem_ofSize (hp _ ha.le) (minors_mem_ofSize o hj h' h _ ha),
    S.mul_mem_ofSize (hp _ ha) (minors_mem_ofSize o hj h' h _ ha.le),
    (S.mul_mem_ofSize (hp _ ha) <| minor_mul_dual_mem_ofSize o hj h' h ha ·)
  simp [prod_range_succ, mul_assoc, -Units.coe_prod] at *; grind [mem_ofSize_mono]

/-- Let K consist of elements of size 1, j ≤ ϱ, s ∈ 𝒩_{<j}, sg ∈ K, and let Q_j w_p⁻¹g meet K.
If p is a head, then g has size 60(ϱ+1)² and w_p⁻¹g has size 99(ϱ+1)². -/
lemma hasMatSize_of_isHead [IsHermUnit T.splitGram]
    (hp : S.IsHead j p) (hν : s ∈ unipotentBelow j) :
  S.HasMatSize (60 * 𝔰.n ^ 2) g.1.1 ∧ S.HasMatSize (99 * 𝔰.n ^ 2) ((weylElem j p)⁻¹ * g).1.1 :=
  (fun a ↦ ⟨a, .mono (.mul (i := 10 * 𝔰.n) (by simp_all [head_entries_mem_ofSize o _ h' h])
  a)⟩) (.mono (by simpa using (HasMatSize.one.sub (hasMatSize_one_sub_inv (r := 1) hν (by simp)
  fun a e ↦ ⟨Pi.single (eStar a) 1, by simpa [-Sum.forall, vecsOfSize] using (sub_mem_ofSize
  (by simp) <| (head_entries_mem_ofSize o hj h' h hp e).2.2 ·)⟩)).mul (o h.2)) (by nlinarith))
