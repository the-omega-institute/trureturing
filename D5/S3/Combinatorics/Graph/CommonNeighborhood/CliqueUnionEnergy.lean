/- GID: D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound]
   utility: none
   digest: A disjoint union of cliques of orders s_i has CN energy 2 sum (s_i - 1)(s_i - 2), at most 2(n - 1)(n - 2), with equality exactly for one clique or two isolated vertices. -/

/- Escape audit unfinished for result: https://github.com/the-omega-institute/trureturing/issues/32710 -/
import D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound

/-! Common-neighbourhood energy of a disjoint union of complete graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.CommonNeighborhood.CliqueUnionEnergy

open Matrix Finset
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
open D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound (psd_difference_bound)

/-
proof_shape:
  cliqueUnion, fibreCard: definitions
  cliqueUnion_decidableRel: private instance
  energy_eq_of_split: content (consumer: result)
  sz, avg, wP, wQ, matP, matQ, total, defect: definitions
  sz_congr, sz_cases, sz_pos, block_sum, sz_two: bind-only (consumers: the block lemmas below)
  avg_conjTranspose, diagonal_comm, posSemidef_of_idem, wP_nonneg, compl_mul_self: bind-only
    (consumers: matP_posSemidef, matQ_posSemidef, result)
  avg_mul_self, matP_posSemidef, matQ_posSemidef, cn_card, cn_apply, split_eq, trace_split,
    trace_value: content (consumer: result)
  defect_bounds: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.psd_difference_bound
    (statement_id sha256:4a61e26c582e3a9997b9d862d130ebfd8cd223970eceb985e8b3f0f6933182cd)
  D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.source_matrix_isHermitian
    (statement_id sha256:f1719f538d0bfd6d4c9cd272d7a3754edc7169f96ade79d35351cea0c770b729)
escape_witness: the trace-duality lower bound sum |lambda_i| >= tr (C S) for -1 <= S <= 1, applied
  to the split C = W Pi - W'(1 - Pi) of the common-neighbour matrix through the clique-averaging
  projection Pi with S = 2 Pi - 1, which pins the energy to tr P + tr Q = 2 sum (s_i - 1)(s_i - 2);
  and the defect recursion g(a + N) - g(a) - g(N) = 2aN - 2 for g(s) = (s - 1)(s - 2), which
  bounds the defect below by (k - 1)(k - 2) + 2(n - k) for k >= 2 cliques.
admission_basis: escape-witness
-/

universe u

/-- The disjoint union of the complete graphs on the fibres of `f`. -/
def cliqueUnion {V : Type} {ι : Type u} (f : V → ι) : SimpleGraph V where
  Adj x y := x ≠ y ∧ f x = f y
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The order of the clique labelled `i`. -/
def fibreCard {V : Type} [Fintype V] {ι : Type u} [DecidableEq ι] (f : V → ι) (i : ι) : ℕ :=
  (univ.filter fun x => f x = i).card

/-- If `C = P - Q` with `P, Q ⪰ 0` and some `S` with `-1 ⪯ S ⪯ 1` has `tr (C S) = tr P + tr Q`,
then the energy of `C` equals `tr P + tr Q`. -/
private theorem energy_eq_of_split {V : Type} [Fintype V] [DecidableEq V]
    {C P Q S : Matrix V V ℝ} (hC : C.IsHermitian) (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPQ : C = P - Q) (hS₁ : (1 + S).PosSemidef) (hS₂ : (1 - S).PosSemidef)
    (htr : (C * S).trace = P.trace + Q.trace) :
    ∑ i, |hC.eigenvalues i| = P.trace + Q.trace := by
  apply le_antisymm
  · subst hPQ
    exact psd_difference_bound P Q hP hQ
  · let U : Matrix V V ℝ := hC.eigenvectorUnitary
    have hUU : U * Uᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff V ℝ).mp hC.eigenvectorUnitary.2
    have hUtU : Uᵀ * U = 1 :=
      (Matrix.mem_orthogonalGroup_iff' V ℝ).mp hC.eigenvectorUnitary.2
    have hdiag : Uᵀ * C * U = Matrix.diagonal hC.eigenvalues := by
      simpa [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using
        hC.conjStarAlgAut_star_eigenvectorUnitary
    have ht (M : Matrix V V ℝ) : (Uᵀ * M * U).trace = M.trace := by
      rw [Matrix.trace_mul_cycle, hUU, one_mul]
    let T := Uᵀ * S * U
    have hconj : (Uᵀ * C * U) * T = Uᵀ * (C * S) * U := by
      simp only [T, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hUU, Matrix.one_mul]
    have hsum : (C * S).trace = ∑ i, hC.eigenvalues i * T i i := by
      rw [← ht (C * S), ← hconj, hdiag]
      simp [Matrix.trace, Matrix.diagonal_mul]
    have hT (i : V) : |T i i| ≤ 1 := by
      have h₁ : (Uᵀ * (1 + S) * U).PosSemidef := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
          hS₁.conjTranspose_mul_mul_same U
      have h₂ : (Uᵀ * (1 - S) * U).PosSemidef := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
          hS₂.conjTranspose_mul_mul_same U
      have e₁ : Uᵀ * (1 + S) * U = 1 + T := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUtU]
      have e₂ : Uᵀ * (1 - S) * U = 1 - T := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUtU]
      have d₁ := h₁.diag_nonneg (i := i)
      have d₂ := h₂.diag_nonneg (i := i)
      rw [e₁] at d₁
      rw [e₂] at d₂
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_eq] at d₁ d₂
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← htr, hsum]
    apply Finset.sum_le_sum
    intro i _
    calc hC.eigenvalues i * T i i ≤ |hC.eigenvalues i * T i i| := le_abs_self _
      _ = |hC.eigenvalues i| * |T i i| := abs_mul _ _
      _ ≤ |hC.eigenvalues i| * 1 := mul_le_mul_of_nonneg_left (hT i) (abs_nonneg _)
      _ = |hC.eigenvalues i| := mul_one _

section Blocks

variable {V : Type} [Fintype V] {ι : Type u} [DecidableEq ι] (f : V → ι)

/-- The order of the clique containing `x`. -/
private def sz (x : V) : ℝ := fibreCard f (f x)

private theorem sz_congr {x z : V} (h : f z = f x) : sz f z = sz f x := by
  unfold sz; rw [h]

private theorem sz_cases (x : V) : sz f x = 1 ∨ 2 ≤ sz f x := by
  have hpos : 0 < fibreCard f (f x) :=
    Finset.card_pos.mpr ⟨x, by simp⟩
  unfold sz
  rcases Nat.lt_or_ge (fibreCard f (f x)) 2 with h | h
  · left; exact_mod_cast (by omega : fibreCard f (f x) = 1)
  · right; exact_mod_cast h

private theorem sz_pos (x : V) : 1 ≤ sz f x := by
  rcases sz_cases f x with h | h <;> linarith

private theorem block_sum (x : V) (g : V → ℝ) (hg : ∀ z, f z = f x → g z = g x) :
    ∑ z, (if f z = f x then g z else 0) = sz f x * g x := by
  rw [← Finset.sum_filter, Finset.sum_congr rfl fun z hz => hg z (mem_filter.mp hz).2,
    Finset.sum_const, nsmul_eq_mul]
  rfl

variable [DecidableEq V]

/-- The orthogonal projection onto vectors constant on each clique. -/
private def avg : Matrix V V ℝ := fun x y => if f x = f y then (sz f x)⁻¹ else 0

omit [DecidableEq V] in
private theorem avg_conjTranspose : (avg f)ᴴ = avg f := by
  ext x y
  simp only [Matrix.conjTranspose_apply, star_trivial, avg]
  split_ifs with h₁ h₂ h₂
  · rw [sz_congr f h₂.symm]
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · rfl

omit [DecidableEq V] in
private theorem avg_mul_self : avg f * avg f = avg f := by
  ext x y
  rw [Matrix.mul_apply]
  have hx : sz f x ≠ 0 := by linarith [sz_pos f x]
  by_cases h : f x = f y
  · have hz : ∀ z, avg f x z * avg f z y =
        if f z = f x then (sz f x)⁻¹ * (sz f x)⁻¹ else 0 := by
      intro z
      simp only [avg]
      by_cases hz : f z = f x
      · rw [ite_eq_left (hz.symm), ite_eq_left ((hz.trans h)), ite_eq_left (hz), sz_congr f hz]
      · rw [ite_eq_right ((Ne.symm hz)), ite_eq_right (hz), zero_mul]
    have hb := block_sum f x (fun _ => (sz f x)⁻¹ * (sz f x)⁻¹) (fun _ _ => rfl)
    rw [Finset.sum_congr rfl fun z _ => hz z, hb]
    simp only [avg, ite_eq_left (h)]
    field_simp
  · rw [Finset.sum_eq_zero]
    · simp only [avg, ite_eq_right (h)]
    · intro z _
      simp only [avg]
      by_cases hz : f x = f z
      · rw [ite_eq_right ((fun h' => h (hz.trans h'))), mul_zero]
      · rw [ite_eq_right (hz), zero_mul]

private theorem diagonal_comm (d : V → ℝ) (hd : ∀ x z, f z = f x → d z = d x) :
    diagonal d * avg f = avg f * diagonal d := by
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [avg]
  by_cases h : f x = f y
  · rw [ite_eq_left (h), hd y x h, mul_comm]
  · rw [ite_eq_right (h), mul_zero, zero_mul]

omit [DecidableEq V] in
private theorem posSemidef_of_idem {A : Matrix V V ℝ} (hA : Aᴴ = A) (hAA : A * A = A) :
    A.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  rwa [hA, hAA] at h

private theorem compl_mul_self : (1 - avg f) * (1 - avg f) = 1 - avg f := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, avg_mul_self]
  abel

/-- The weight on the projection part: `(s - 2)(s - 1)`. -/
private def wP (x : V) : ℝ := (sz f x - 2) * (sz f x - 1)

/-- The weight on the complementary part: `max (s - 2) 0`. -/
private def wQ (x : V) : ℝ := max (sz f x - 2) 0

private def matP : Matrix V V ℝ := diagonal (wP f) * avg f

private def matQ : Matrix V V ℝ := diagonal (wQ f) * (1 - avg f)

omit [DecidableEq V] in
private theorem wP_nonneg (x : V) : 0 ≤ wP f x := by
  unfold wP
  rcases sz_cases f x with h | h
  · rw [h]; norm_num
  · exact mul_nonneg (by linarith) (by linarith)

private theorem matP_posSemidef : (matP f).PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal (wP_nonneg f)).conjTranspose_mul_mul_same (avg f)
  rw [avg_conjTranspose, ← diagonal_comm f _ (fun x z hz => by simp only [wP, sz_congr f hz]),
    Matrix.mul_assoc, avg_mul_self] at h
  exact h

private theorem matQ_posSemidef : (matQ f).PosSemidef := by
  have hw : ∀ x, 0 ≤ wQ f x := fun x => le_max_right _ _
  have h := (Matrix.PosSemidef.diagonal hw).conjTranspose_mul_mul_same (1 - avg f)
  have hc : diagonal (wQ f) * (1 - avg f) = (1 - avg f) * diagonal (wQ f) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      diagonal_comm f _ (fun x z hz => by simp only [wQ, sz_congr f hz])]
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, avg_conjTranspose, ← hc,
    Matrix.mul_assoc, compl_mul_self] at h
  exact h

omit [DecidableEq V] in
private theorem sz_two {x y : V} (hxy : x ≠ y) (h : f x = f y) : 2 ≤ sz f x := by
  rcases sz_cases f x with hs | hs
  · exfalso
    have h1 : fibreCard f (f x) = 1 := by unfold sz at hs; exact_mod_cast hs
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    have hx : x ∈ univ.filter fun z => f z = f x := by simp
    have hy : y ∈ univ.filter fun z => f z = f x := by simp [h]
    rw [ha, mem_singleton] at hx hy
    exact hxy (hx.trans hy.symm)
  · exact hs

private instance cliqueUnion_decidableRel : DecidableRel (cliqueUnion f).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ f x = f y))

/-- Distinct vertices of one clique of order `s` have `s - 2` common neighbours, and vertices
of different cliques have none. -/
private theorem cn_card (x y : V) (hxy : x ≠ y) :
    (((univ.filter fun k => k ≠ x ∧ k ≠ y ∧ (cliqueUnion f).Adj x k ∧
        (cliqueUnion f).Adj y k).card : ℕ) : ℝ) = if f x = f y then sz f x - 2 else 0 := by
  by_cases h : f x = f y
  · rw [ite_eq_left h]
    have hset : (univ.filter fun k => k ≠ x ∧ k ≠ y ∧ (cliqueUnion f).Adj x k ∧
        (cliqueUnion f).Adj y k) =
        ((univ.filter fun z => f z = f x).erase x).erase y := by
      ext k
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      constructor
      · rintro ⟨hkx, hky, hxk, -⟩
        exact ⟨hky, hkx, hxk.2.symm⟩
      · rintro ⟨hky, hkx, hk⟩
        exact ⟨hkx, hky, ⟨Ne.symm hkx, hk.symm⟩, ⟨Ne.symm hky, h ▸ hk.symm⟩⟩
    have hy : y ∈ (univ.filter fun z => f z = f x).erase x := by
      simp only [mem_erase, mem_filter, mem_univ, true_and]
      exact ⟨Ne.symm hxy, h.symm⟩
    have hx : x ∈ univ.filter fun z => f z = f x := by simp
    have c₁ := Finset.card_erase_add_one hy
    have c₂ := Finset.card_erase_add_one hx
    rw [hset]
    have : (((((univ.filter fun z => f z = f x).erase x).erase y).card : ℕ) : ℝ) + 1 + 1 =
        sz f x := by
      unfold sz fibreCard
      exact_mod_cast (by omega)
    linarith
  · rw [ite_eq_right h]
    have hz : (univ.filter fun k => k ≠ x ∧ k ≠ y ∧ (cliqueUnion f).Adj x k ∧
        (cliqueUnion f).Adj y k).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro k _ hk
      exact h (hk.2.2.1.2.trans hk.2.2.2.2.symm)
    rw [hz]
    simp

/-- The common-neighbour entry between distinct vertices of one clique is `s - 2`. -/
private theorem cn_apply (x y : V) :
    commonNeighbourMatrix (cliqueUnion f) x y =
      if x = y then 0 else if f x = f y then sz f x - 2 else 0 := by
  unfold commonNeighbourMatrix
  by_cases hxy : x = y
  · simp [hxy]
  · rw [ite_eq_right hxy, ite_eq_right hxy]
    convert cn_card f x y hxy

private theorem split_eq : commonNeighbourMatrix (cliqueUnion f) = matP f - matQ f := by
  ext x y
  rw [cn_apply, Matrix.sub_apply, matP, matQ, Matrix.diagonal_mul, Matrix.diagonal_mul]
  simp only [avg, Matrix.sub_apply, Matrix.one_apply]
  have hx : sz f x ≠ 0 := by linarith [sz_pos f x]
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte]
    rcases sz_cases f x with hs | hs
    · simp only [wP, wQ, hs]; norm_num
    · rw [wQ, max_eq_left (by linarith), wP]
      field_simp
      ring
  · have hsym : ¬ f x = f y ∨ 2 ≤ sz f x := by
      by_cases h : f x = f y
      · exact Or.inr (sz_two f hxy h)
      · exact Or.inl h
    simp only [ite_eq_right (hxy)]
    by_cases h : f x = f y
    · rw [ite_eq_left (h), ite_eq_left (h), wQ, max_eq_left (by linarith [sz_two f hxy h]), wP]
      field_simp
      ring
    · rw [ite_eq_right (h), ite_eq_right (h)]; ring

private theorem trace_split :
    ((matP f - matQ f) * ((2 : ℝ) • avg f - 1)).trace = (matP f).trace + (matQ f).trace := by
  have hAA := avg_mul_self f
  have hP : matP f * ((2 : ℝ) • avg f - 1) = matP f := by
    rw [matP, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_smul, hAA, Matrix.mul_one, two_smul,
      add_sub_cancel_right]
  have hQ : matQ f * ((2 : ℝ) • avg f - 1) = -matQ f := by
    have h0 : (1 - avg f) * avg f = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hAA, sub_self]
    rw [matQ, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_smul, h0, smul_zero, Matrix.mul_one,
      zero_sub, Matrix.mul_neg]
  rw [Matrix.sub_mul, hP, hQ, sub_neg_eq_add, Matrix.trace_add]

private theorem trace_value :
    (matP f).trace + (matQ f).trace =
      2 * ∑ i ∈ univ.image f, ((fibreCard f i : ℝ) - 1) * ((fibreCard f i : ℝ) - 2) := by
  have hpt : ∀ x, matP f x x + matQ f x x = 2 * (sz f x - 1) * (sz f x - 2) / sz f x := by
    intro x
    have hx : sz f x ≠ 0 := by linarith [sz_pos f x]
    simp only [matP, matQ, Matrix.diagonal_mul, avg, ↓reduceIte, Matrix.sub_apply,
      Matrix.one_apply_eq]
    rcases sz_cases f x with hs | hs
    · simp only [wP, wQ, hs]; norm_num
    · rw [wQ, max_eq_left (by linarith), wP]
      field_simp
      ring
  rw [Matrix.trace, Matrix.trace, ← Finset.sum_add_distrib]
  change ∑ x, (matP f x x + matQ f x x) = _
  rw [Finset.sum_congr rfl fun x _ => hpt x,
    ← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ.image f)
      (fun x _ => mem_image_of_mem f (mem_univ x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hcard : (fibreCard f i : ℝ) ≠ 0 := by
    obtain ⟨x, -, rfl⟩ := mem_image.mp hi
    exact_mod_cast (Finset.card_pos.mpr ⟨x, by simp⟩).ne'
  rw [Finset.sum_congr rfl fun x hx => by
    rw [show sz f x = fibreCard f i by unfold sz; rw [(mem_filter.mp hx).2]]]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (fibreCard f i : ℝ) * _ = _
  field_simp

end Blocks

private def total {ι : Type u} (m : ι → ℤ) (t : Finset ι) : ℤ := ∑ i ∈ t, m i

private def defect {ι : Type u} (m : ι → ℤ) (t : Finset ι) : ℤ :=
  (total m t - 1) * (total m t - 2) - ∑ i ∈ t, (m i - 1) * (m i - 2)

/-- The defect `g(Σ m) - Σ g(m)` of `g(s) = (s - 1)(s - 2)` is `2` for no parts, `0` for one
part, and at least `(k - 1)(k - 2) + 2(N - k)` for `k ≥ 2` parts of total `N`. -/
private theorem defect_bounds {ι : Type u} [DecidableEq ι] (m : ι → ℤ) (t : Finset ι)
    (hm : ∀ i ∈ t, 1 ≤ m i) :
    (t.card : ℤ) ≤ total m t ∧ (t.card = 0 → defect m t = 2) ∧
      (t.card = 1 → defect m t = 0) ∧
      (2 ≤ t.card → ((t.card : ℤ) - 1) * ((t.card : ℤ) - 2) + 2 * (total m t - t.card) ≤
        defect m t) := by
  induction t using Finset.induction_on with
  | empty => simp [total, defect]
  | insert a t ha ih =>
    have hma := hm a (mem_insert_self a t)
    obtain ⟨hT, h0, h1, h2⟩ := ih fun i hi => hm i (mem_insert_of_mem hi)
    have htot : total m (insert a t) = m a + total m t := by
      simp only [total, sum_insert ha]
    have hdef : defect m (insert a t) = defect m t + 2 * m a * total m t - 2 := by
      simp only [defect, total, sum_insert ha]; ring
    have hcard : (insert a t).card = t.card + 1 := card_insert_of_notMem ha
    rw [htot, hdef, hcard]
    push_cast
    refine ⟨by linarith, fun h => by simp at h, fun hc => ?_, fun hc => ?_⟩
    · have ht : t.card = 0 := by omega
      have hT0 : total m t = 0 := by
        rw [Finset.card_eq_zero.mp ht]; simp [total]
      rw [h0 ht, hT0]; ring
    · rcases Nat.lt_or_ge t.card 2 with hk | hk
      · have ht : t.card = 1 := by omega
        rw [h1 ht, ht]
        have hT1 : 1 ≤ total m t := by rw [ht] at hT; exact_mod_cast hT
        push_cast
        nlinarith
      · have hb := h2 hk
        have hk' : (2 : ℤ) ≤ t.card := by exact_mod_cast hk
        nlinarith [mul_le_mul_of_nonneg_left hT (by linarith : (0 : ℤ) ≤ m a - 1)]

/-- The disjoint union of cliques `K_{s_i}` (the fibres of `f`) on `n` vertices has
common-neighbourhood energy `2 Σ (s_i - 1)(s_i - 2)`; this is at most `2(n - 1)(n - 2)`, with
equality exactly when there is one clique, or two cliques that are both single vertices. -/
theorem result {V : Type} [Fintype V] {ι : Type u} [DecidableEq ι] (f : V → ι) :
    graphEnergy (cliqueUnion f) .commonNeighbour =
        2 * ∑ i ∈ univ.image f, ((fibreCard f i : ℝ) - 1) * ((fibreCard f i : ℝ) - 2) ∧
      graphEnergy (cliqueUnion f) .commonNeighbour ≤
        2 * ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 2) ∧
      (graphEnergy (cliqueUnion f) .commonNeighbour =
          2 * ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 2) ↔
        (univ.image f).card = 1 ∨
          ((univ.image f).card = 2 ∧ ∀ i ∈ univ.image f, fibreCard f i = 1)) := by
  classical
  have hC := source_matrix_isHermitian (cliqueUnion f) .commonNeighbour
  have he : graphEnergy (cliqueUnion f) .commonNeighbour = ∑ i, |hC.eigenvalues i| := by
    simp [graphEnergy, graphSpectrum, Multiset.map_map]
  have hsplit : sourceMatrix (cliqueUnion f) .commonNeighbour = matP f - matQ f :=
    split_eq f
  have hS₁ : (1 + ((2 : ℝ) • avg f - 1)).PosSemidef := by
    rw [add_sub_cancel]
    exact (posSemidef_of_idem (avg_conjTranspose f) (avg_mul_self f)).smul (by norm_num)
  have hS₂ : (1 - ((2 : ℝ) • avg f - 1)).PosSemidef := by
    have hI : (1 - avg f)ᴴ = 1 - avg f := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, avg_conjTranspose]
    have h2 : (1 : Matrix V V ℝ) - ((2 : ℝ) • avg f - 1) = (2 : ℝ) • (1 - avg f) := by
      rw [smul_sub, two_smul, two_smul]; abel
    rw [h2]
    exact (posSemidef_of_idem hI (compl_mul_self f)).smul (by norm_num)
  have hE := energy_eq_of_split hC (matP_posSemidef f) (matQ_posSemidef f) hsplit hS₁ hS₂
    (by rw [hsplit]; exact trace_split f)
  have hval : graphEnergy (cliqueUnion f) .commonNeighbour =
      2 * ∑ i ∈ univ.image f, ((fibreCard f i : ℝ) - 1) * ((fibreCard f i : ℝ) - 2) := by
    rw [he, hE, trace_value]
  -- Integer arithmetic over the clique orders.
  let t := univ.image f
  let m : ι → ℤ := fun i => fibreCard f i
  have hm : ∀ i ∈ t, 1 ≤ m i := by
    intro i hi
    obtain ⟨x, -, rfl⟩ := mem_image.mp hi
    have hp : 0 < fibreCard f (f x) := Finset.card_pos.mpr ⟨x, by simp⟩
    show (1 : ℤ) ≤ (fibreCard f (f x) : ℤ)
    omega
  have hN : total m t = Fintype.card V := by
    simp only [total, m, t]
    rw [← Finset.card_univ, Finset.card_eq_sum_card_image f univ]
    push_cast
    rfl
  have hgap : 2 * ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 2) -
      graphEnergy (cliqueUnion f) .commonNeighbour = 2 * (defect m t : ℝ) := by
    rw [hval, defect, hN]
    simp only [m, t]
    push_cast
    ring
  obtain ⟨hT, h0, h1, h2⟩ := defect_bounds m t hm
  have hnonneg : 0 ≤ defect m t := by
    rcases Nat.lt_or_ge t.card 2 with hk | hk
    · rcases (by omega : t.card = 0 ∨ t.card = 1) with hc | hc
      · rw [h0 hc]; norm_num
      · rw [h1 hc]
    · have hb := h2 hk
      have hk' : (2 : ℤ) ≤ t.card := by exact_mod_cast hk
      nlinarith
  refine ⟨hval, ?_, ?_⟩
  · have : (0 : ℝ) ≤ defect m t := by exact_mod_cast hnonneg
    linarith
  · have hiff : graphEnergy (cliqueUnion f) .commonNeighbour =
        2 * ((Fintype.card V : ℝ) - 1) * ((Fintype.card V : ℝ) - 2) ↔ defect m t = 0 := by
      constructor
      · intro h
        have : (defect m t : ℝ) = 0 := by linarith
        exact_mod_cast this
      · intro h
        have : (defect m t : ℝ) = 0 := by exact_mod_cast h
        linarith
    rw [hiff]
    change defect m t = 0 ↔ t.card = 1 ∨ (t.card = 2 ∧ ∀ i ∈ t, fibreCard f i = 1)
    constructor
    · intro hd
      rcases Nat.lt_or_ge t.card 3 with hk | hk
      · rcases (by omega : t.card = 0 ∨ t.card = 1 ∨ t.card = 2) with hc | hc | hc
        · rw [h0 hc] at hd; norm_num at hd
        · exact Or.inl hc
        · right
          refine ⟨hc, fun i hi => ?_⟩
          have hb := h2 (by omega)
          rw [hc] at hb
          have hT2 : total m t ≤ 2 := by push_cast at hb; linarith
          have hsum : ∑ j ∈ t, (m j - 1) = 0 := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, hc, nsmul_eq_mul]
            simp only [total] at hT2 hT
            push_cast
            linarith
          have hz := (Finset.sum_eq_zero_iff_of_nonneg
            (fun j hj => by linarith [hm j hj])).mp hsum i hi
          have : (fibreCard f i : ℤ) = 1 := by change m i = 1; linarith
          exact_mod_cast this
      · have hb := h2 (by omega)
        have hk' : (3 : ℤ) ≤ t.card := by exact_mod_cast hk
        nlinarith
    · rintro (hc | ⟨hc, hall⟩)
      · exact h1 hc
      · have hm1 : ∀ i ∈ t, m i = 1 := fun i hi => by simp only [m, hall i hi]; norm_num
        simp only [defect, total, Finset.sum_congr rfl hm1, sum_const, hc]
        norm_num
        exact Finset.sum_eq_zero fun i hi => by rw [hm1 i hi]; norm_num

#print axioms result

end D5.S3.Combinatorics.Graph.CommonNeighborhood.CliqueUnionEnergy
