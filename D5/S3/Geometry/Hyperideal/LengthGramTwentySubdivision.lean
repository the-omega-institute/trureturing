/- GID: D5/S3/Geometry/Hyperideal/LengthGramTwentySubdivision
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramTwentySubdivision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Join]
   utility: none
   digest: The literal twenty closed tetrahedra in the original six-length coefficient body. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramTwentySubdivision

abbrev V := Fin 4 → ℝ
abbrev Support := Fin 4 ⊕ Fin 4

def barycenter : V := fun _ => 1 / 4

/-- One fixed ambient affine space, shared by every cell. -/
def sumOne : AffineSubspace ℝ V where
  carrier := {x | ∑ i, x i = 1}
  smul_vsub_vadd_mem' c p q r hp hq hr := by
    change (∑ i, c * (p i - q i) + r i) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, hq, hr]
    ring

def support (l : Fin 6 → ℝ) : Support → V →ₗ[ℝ] ℝ
  | Sum.inl i => -(LinearMap.proj i)
  | Sum.inr i => ∑ j, lengthGram l i j • LinearMap.proj j

/-- Zero-incidence of the twelve original ordered endpoints with the eight supports. -/
def incident : Support → Fin 4 → Fin 4 → Prop
  | Sum.inl k, i, j => k ≠ i ∧ k ≠ j
  | Sum.inr k, i, _ => k = i

instance (f : Support) (i j : Fin 4) : Decidable (incident f i j) := by
  cases f <;> dsimp [incident] <;> infer_instance

/-- The original Scribe's twenty tuples, in its original order. -/
def vertices (l : Fin 6 → ℝ) : Fin 20 → Fin 4 → V :=
  ![![barycenter, endpoint l 0 1, endpoint l 0 2, endpoint l 0 3],
    ![barycenter, endpoint l 1 0, endpoint l 1 2, endpoint l 1 3],
    ![barycenter, endpoint l 2 0, endpoint l 2 1, endpoint l 2 3],
    ![barycenter, endpoint l 3 0, endpoint l 3 1, endpoint l 3 2],
    ![barycenter, endpoint l 1 2, endpoint l 2 1, endpoint l 2 3],
    ![barycenter, endpoint l 1 2, endpoint l 2 3, endpoint l 3 2],
    ![barycenter, endpoint l 1 2, endpoint l 3 2, endpoint l 3 1],
    ![barycenter, endpoint l 1 2, endpoint l 3 1, endpoint l 1 3],
    ![barycenter, endpoint l 0 2, endpoint l 2 0, endpoint l 2 3],
    ![barycenter, endpoint l 0 2, endpoint l 2 3, endpoint l 3 2],
    ![barycenter, endpoint l 0 2, endpoint l 3 2, endpoint l 3 0],
    ![barycenter, endpoint l 0 2, endpoint l 3 0, endpoint l 0 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 0, endpoint l 1 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 3, endpoint l 3 1],
    ![barycenter, endpoint l 0 1, endpoint l 3 1, endpoint l 3 0],
    ![barycenter, endpoint l 0 1, endpoint l 3 0, endpoint l 0 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 0, endpoint l 1 2],
    ![barycenter, endpoint l 0 1, endpoint l 1 2, endpoint l 2 1],
    ![barycenter, endpoint l 0 1, endpoint l 2 1, endpoint l 2 0],
    ![barycenter, endpoint l 0 1, endpoint l 2 0, endpoint l 0 2]]

def cell (l : Fin 6 → ℝ) (n : Fin 20) : Set V :=
  convexHull ℝ (range (vertices l n))

def boundaryTriangle (l : Fin 6 → ℝ) (n : Fin 20) : Set V :=
  convexHull ℝ (range (fun j : Fin 3 => vertices l n j.succ))

def facet : Fin 20 → Support :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3,
    Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0,
    Sum.inl 1, Sum.inl 1, Sum.inl 1, Sum.inl 1,
    Sum.inl 2, Sum.inl 2, Sum.inl 2, Sum.inl 2,
    Sum.inl 3, Sum.inl 3, Sum.inl 3, Sum.inl 3]

/-- The support of the opposite edge of each boundary triangle. -/
def ridge : Fin 20 → Support :=
  ![Sum.inl 1, Sum.inl 0, Sum.inl 0, Sum.inl 0,
    Sum.inr 2, Sum.inl 1, Sum.inr 3, Sum.inl 2,
    Sum.inr 2, Sum.inl 0, Sum.inr 3, Sum.inl 2,
    Sum.inr 1, Sum.inl 0, Sum.inr 3, Sum.inl 1,
    Sum.inr 1, Sum.inl 0, Sum.inr 2, Sum.inl 1]

def capIndex (i : Fin 4) : Fin 20 := ⟨i.val, by omega⟩
def sideIndex (k r : Fin 4) : Fin 20 := ⟨4 + 4 * k.val + r.val, by omega⟩

def sideOrder (k : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (![![0,1,2,3], ![1,0,2,3], ![2,0,1,3], ![3,0,1,2]] k)
    (by fin_cases k <;> decide)

/-- The four original six-vertex endpoint cycles, without changing any vertex. -/
def sideCycle (l : Fin 6 → ℝ) (k : Fin 4) : Fin 6 → V :=
  let σ := sideOrder k
  ![endpoint l (σ 1) (σ 2), endpoint l (σ 2) (σ 1),
    endpoint l (σ 2) (σ 3), endpoint l (σ 3) (σ 2),
    endpoint l (σ 3) (σ 1), endpoint l (σ 1) (σ 3)]

/-- Supporting traces of all six edges in each original cyclic order. -/
def cycleSupport (k : Fin 4) : Fin 6 → Support :=
  let σ := sideOrder k
  ![Sum.inl (σ 3), Sum.inr (σ 2), Sum.inl (σ 1),
    Sum.inr (σ 3), Sum.inl (σ 2), Sum.inr (σ 1)]

private def row (l : Fin 6 → ℝ) (i : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  ∑ j, lengthGram l i j * x j

private lemma row_line (l : Fin 6 → ℝ) (i : Fin 4)
    (a x : Fin 4 → ℝ) (u : ℝ) :
    row l i (fun j => a j + u * (x j - a j)) =
      row l i a + u * (row l i x - row l i a) := by
  simp only [row, Fin.sum_univ_succ]
  ring

/-- The ratio maximizer constructs an exit point; supports already zero at
the anchor remain nonpositive throughout the extension. -/
private lemma support_ray {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (L : ι → (Fin 4 → ℝ) → ℝ)
    (a x : Fin 4 → ℝ)
    (hline : ∀ r u, L r (fun j => a j + u * (x j - a j)) =
      L r a + u * (L r x - L r a))
    (ha : ∀ r ∈ S, L r a < 0)
    (hzero : ∀ r, r ∉ S → L r a = 0)
    (hx : ∀ r, L r x ≤ 0)
    (hgrowth : ∃ r ∈ S, L r a < L r x) :
    ∃ r ∈ S, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = (L r x - L r a) / (-L r a) ∧
      (∀ s ∈ S, (L s x - L s a) / (-L s a) ≤ t) ∧
      (∀ s, L s (fun j => a j + (x j - a j) / t) ≤ 0) ∧
      L r (fun j => a j + (x j - a j) / t) = 0 ∧
      x = (1 - t) • a + t • (fun j => a j + (x j - a j) / t) := by
  obtain ⟨s, hs, hsa⟩ := hgrowth
  obtain ⟨r, hr, hmax⟩ := S.exists_max_image
    (fun r => (L r x - L r a) / (-L r a)) ⟨s, hs⟩
  let t := (L r x - L r a) / (-L r a)
  have ht : 0 < t := lt_of_lt_of_le
    (div_pos (sub_pos.mpr hsa) (neg_pos.mpr (ha s hs))) (hmax s hs)
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ (neg_pos.mpr (ha r hr))).mpr
    linarith [hx r]
  have hformula (s : ι) :
      L s (fun j => a j + (x j - a j) / t) =
        L s a + (L s x - L s a) / t := by
    simpa only [div_eq_mul_inv, mul_comm] using hline s t⁻¹
  have hle (s : ι) : L s (fun j => a j + (x j - a j) / t) ≤ 0 := by
    rw [hformula]
    by_cases hs : s ∈ S
    · have hh := (div_le_iff₀ (neg_pos.mpr (ha s hs))).mp (hmax s hs)
      have hd : (L s x - L s a) / t ≤ -L s a := by
        apply (div_le_iff₀ ht).mpr
        nlinarith only [hh]
      linarith
    · rw [hzero s hs, sub_zero, zero_add]
      exact div_nonpos_of_nonpos_of_nonneg (hx s) ht.le
  have heq : L r (fun j => a j + (x j - a j) / t) = 0 := by
    rw [hformula]
    have hta : t * (-L r a) = L r x - L r a := by
      exact div_mul_cancel₀ _ (neg_pos.mpr (ha r hr)).ne'
    have hquot : (L r x - L r a) / t = -L r a := by
      apply (div_eq_iff ht.ne').mpr
      nlinarith only [hta]
    rw [hquot]
    ring
  refine ⟨r, hr, t, ht, ht1, rfl, hmax, hle, heq, ?_⟩
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ht.ne']
  ring

/-- Every point different from the original barycenter has an explicit
support-ratio extension to one of the eight original supporting traces. -/
private theorem barycenter_ray_exit (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (x : Fin 4 → ℝ) (hx : x ∈ cutBody l)
    (hxb : x ≠ fun _ : Fin 4 => (1 : ℝ) / 4) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      let y : Fin 4 → ℝ := fun j => 1 / 4 + (x j - 1 / 4) / t
      y ∈ cutBody l ∧
      ((∃ i, y i = 0) ∨ (∃ i, (∑ j, lengthGram l i j * y j) = 0)) ∧
      x = (1 - t) • (fun _ : Fin 4 => (1 : ℝ) / 4) + t • y := by
  classical
  let b : Fin 4 → ℝ := fun _ => 1 / 4
  let L : (Fin 4 ⊕ Fin 4) → (Fin 4 → ℝ) → ℝ :=
    Sum.elim (fun i v => -v i) (row l)
  have hsumx := hx.1.2
  have hsmall : ∃ i, x i < (1 : ℝ) / 4 := by
    by_contra hn
    push_neg at hn
    have hx0 := hn 0
    have hx1 := hn 1
    have hx2 := hn 2
    have hx3 := hn 3
    simp only [Fin.sum_univ_succ] at hsumx
    apply hxb
    funext i
    fin_cases i <;> dsimp <;> linarith
  have hline (r : Fin 4 ⊕ Fin 4) (u : ℝ) :
      L r (fun j => b j + u * (x j - b j)) =
        L r b + u * (L r x - L r b) := by
    cases r with
    | inl i => dsimp [L]; ring
    | inr i => exact row_line l i b x u
  have hb (r : Fin 4 ⊕ Fin 4) : L r b < 0 := by
    cases r with
    | inl i => norm_num [L, b]
    | inr i => exact (shared_radial_body l hl).2.2.1 i
  have hLx (r : Fin 4 ⊕ Fin 4) : L r x ≤ 0 := by
    cases r with
    | inl i => exact neg_nonpos.mpr (hx.1.1 i)
    | inr i => exact hx.2 i
  obtain ⟨i, hi⟩ := hsmall
  have hgrowth : ∃ r ∈ (Finset.univ : Finset (Fin 4 ⊕ Fin 4)), L r b < L r x :=
    ⟨Sum.inl i, Finset.mem_univ _, neg_lt_neg hi⟩
  obtain ⟨r, _, t, ht, ht1, _, _, hLy, hry, hxy⟩ :=
    support_ray Finset.univ L b x hline (fun r _ => hb r)
      (by intro r hr; exact (hr (Finset.mem_univ r)).elim) hLx hgrowth
  let y : Fin 4 → ℝ := fun j => 1 / 4 + (x j - 1 / 4) / t
  have hysum : ∑ j, y j = 1 := by
    have hfour : (∑ _ : Fin 4, (1 : ℝ) / 4) = 1 := by norm_num
    dsimp [y]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      hfour, hx.1.2]
    simp
  refine ⟨t, ht, ht1, ?_⟩
  change y ∈ cutBody l ∧ _ ∧ _
  refine ⟨⟨⟨?_, hysum⟩, ?_⟩, ?_, hxy⟩
  · intro j
    exact neg_nonpos.mp (hLy (Sum.inl j))
  · intro j
    exact hLy (Sum.inr j)
  · cases r with
    | inl j => exact Or.inl ⟨j, neg_eq_zero.mp hry⟩
    | inr j => exact Or.inr ⟨j, hry⟩

/-- On the original side omitted by `sigma 0`, extend from the literal
endpoint near `sigma 1` towards any other side point. The exit belongs to
one of the four edges opposite that fan vertex, with the original support
order cap-j, side-i, cap-h, side-j. -/
private theorem side_fan_ray_exit (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (sigma : Equiv.Perm (Fin 4)) (x : Fin 4 → ℝ)
    (hx : x ∈ cutBody l) (hxk : x (sigma 0) = 0)
    (hxa : x ≠ endpoint l (sigma 1) (sigma 2)) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      let a := endpoint l (sigma 1) (sigma 2)
      let y : Fin 4 → ℝ := fun s => a s + (x s - a s) / t
      y ∈ cutBody l ∧ y (sigma 0) = 0 ∧
      ((∑ s, lengthGram l (sigma 2) s * y s) = 0 ∨
        y (sigma 1) = 0 ∨
        (∑ s, lengthGram l (sigma 3) s * y s) = 0 ∨
        y (sigma 2) = 0) ∧
      x = (1 - t) • a + t • y := by
  classical
  let k := sigma 0
  let i := sigma 1
  let j := sigma 2
  let h := sigma 3
  have hne (r s : Fin 4) (hrs : r ≠ s) : sigma r ≠ sigma s :=
    fun heq => hrs (sigma.injective heq)
  let a := endpoint l i j
  obtain ⟨ha, hai, haj, haz, har, hao⟩ :=
    (cut_body_polytope l hl).2.2.2 i j (hne 1 2 (by decide))
  have hak : a k = 0 := haz k (hne 0 1 (by decide)) (hne 0 2 (by decide))
  have hah : a h = 0 := haz h (hne 3 1 (by decide)) (hne 3 2 (by decide))
  have hsum (v : Fin 4 → ℝ) : (∑ s, v (sigma s)) = ∑ s, v s :=
    Equiv.sum_comp sigma v
  have hxsum : x i + x j + x h = 1 := by
    have hh := (hsum x).trans hx.1.2
    simp only [Fin.sum_univ_succ] at hh
    change x k + (x i + (x j + (x h + 0))) = 1 at hh
    rw [hxk] at hh
    linarith
  have hasum : a i + a j = 1 := by
    have hh := (hsum a).trans ha.1.2
    simp only [Fin.sum_univ_succ] at hh
    change a k + (a i + (a j + (a h + 0))) = 1 at hh
    rw [hak, hah] at hh
    linarith
  have hgrowth : x i < a i ∨ x j < a j := by
    by_contra hn
    push_neg at hn
    have hxhn := hx.1.1 h
    have hxi : x i = a i := by linarith
    have hxj : x j = a j := by linarith
    have hxh : x h = 0 := by linarith
    apply hxa
    funext s
    obtain ⟨r, rfl⟩ := sigma.surjective s
    fin_cases r
    · exact hxk.trans hak.symm
    · exact hxi
    · exact hxj
    · exact hxh.trans hah.symm
  let L : Fin 6 → (Fin 4 → ℝ) → ℝ :=
    ![(fun v => -v i), (fun v => -v j), (fun v => -v h),
      row l i, row l j, row l h]
  let S : Finset (Fin 6) := {0, 1, 4, 5}
  have hline (r : Fin 6) (u : ℝ) :
      L r (fun s => a s + u * (x s - a s)) =
        L r a + u * (L r x - L r a) := by
    fin_cases r
    · dsimp [L]; ring
    · dsimp [L]; ring
    · dsimp [L]; ring
    · exact row_line l i a x u
    · exact row_line l j a x u
    · exact row_line l h a x u
  have hLa : ∀ r ∈ S, L r a < 0 := by
    intro r hr
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · change -a i < 0
      linarith only [hai]
    · change -a j < 0
      linarith only [haj]
    · exact hao j (hne 2 1 (by decide))
    · exact hao h (hne 3 1 (by decide))
  have hzero : ∀ r, r ∉ S → L r a = 0 := by
    intro r hr
    fin_cases r
    · exact (hr (by simp [S])).elim
    · exact (hr (by simp [S])).elim
    · change -a h = 0
      rw [hah, neg_zero]
    · exact har
    · exact (hr (by simp [S])).elim
    · exact (hr (by simp [S])).elim
  have hLx (r : Fin 6) : L r x ≤ 0 := by
    fin_cases r
    · exact neg_nonpos.mpr (hx.1.1 i)
    · exact neg_nonpos.mpr (hx.1.1 j)
    · exact neg_nonpos.mpr (hx.1.1 h)
    · exact hx.2 i
    · exact hx.2 j
    · exact hx.2 h
  have hg : ∃ r ∈ S, L r a < L r x := by
    rcases hgrowth with hi | hj
    · exact ⟨0, by simp [S], neg_lt_neg hi⟩
    · exact ⟨1, by simp [S], neg_lt_neg hj⟩
  obtain ⟨r, hr, t, ht, ht1, _, _, hLy, hry, hxy⟩ :=
    support_ray S L a x hline hLa hzero hLx hg
  let y : Fin 4 → ℝ := fun s => a s + (x s - a s) / t
  have hyk : y k = 0 := by simp [y, hak, hxk]
  have hyi : 0 ≤ y i := neg_nonpos.mp (hLy 0)
  have hyj : 0 ≤ y j := neg_nonpos.mp (hLy 1)
  have hyh : 0 ≤ y h := neg_nonpos.mp (hLy 2)
  have hypos (s : Fin 4) : 0 ≤ y s := by
    obtain ⟨r, rfl⟩ := sigma.surjective s
    fin_cases r
    · rw [hyk]
    · exact hyi
    · exact hyj
    · exact hyh
  have hysum : ∑ s, y s = 1 := by
    dsimp [y]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      hx.1.2, ha.1.2]
    simp
  have hoff (r s : Fin 4) (hrs : r ≠ s) : lengthGram l r s < -1 := by
    have hc (q : Fin 6) : 1 < Real.cosh (l q) :=
      Real.one_lt_cosh.mpr (ne_of_gt (hl q))
    fin_cases r <;> fin_cases s <;> first
      | exact (hrs rfl).elim
      | exact neg_lt_neg (hc 0)
      | exact neg_lt_neg (hc 1)
      | exact neg_lt_neg (hc 2)
      | exact neg_lt_neg (hc 3)
      | exact neg_lt_neg (hc 4)
      | exact neg_lt_neg (hc 5)
  have hyrowk : row l k y ≤ 0 := by
    apply Finset.sum_nonpos
    intro s _
    by_cases hsk : s = k
    · rw [hsk, hyk, mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg
        (le_trans (hoff k s hsk.symm).le (by norm_num)) (hypos s)
  have hycut : ∀ r, row l r y ≤ 0 := by
    intro s
    obtain ⟨r, rfl⟩ := sigma.surjective s
    fin_cases r
    · exact hyrowk
    · exact hLy 3
    · exact hLy 4
    · exact hLy 5
  refine ⟨t, ht, ht1, ?_⟩
  change y ∈ cutBody l ∧ y k = 0 ∧ _ ∧ _
  refine ⟨⟨⟨hypos, hysum⟩, hycut⟩, hyk, ?_, hxy⟩
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (neg_eq_zero.mp hry))
  · exact Or.inr (Or.inr (Or.inr (neg_eq_zero.mp hry)))
  · exact Or.inl hry
  · exact Or.inr (Or.inr (Or.inl hry))


private lemma support_body (l : Fin 6 → ℝ) (x : V) (hx : x ∈ cutBody l)
    (f : Support) : support l f x ≤ 0 := by
  cases f with
  | inl i => exact neg_nonpos.mpr (hx.1.1 i)
  | inr i => simpa [support] using hx.2 i

private lemma support_barycenter (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) : support l f barycenter < 0 := by
  cases f with
  | inl i => norm_num [support, barycenter]
  | inr i => simpa [support, barycenter] using (shared_radial_body l hl).2.2.1 i

private lemma endpoint_support (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    (incident f i j → support l f (endpoint l i j) = 0) ∧
    (¬ incident f i j → support l f (endpoint l i j) < 0) := by
  obtain ⟨_, hi, hj, hz, hr, ho⟩ := (cut_body_polytope l hl).2.2.2 i j hij
  cases f with
  | inl k =>
    constructor
    · rintro ⟨hki, hkj⟩
      simpa [support] using congrArg Neg.neg (hz k hki hkj)
    · intro h
      by_cases hki : k = i
      · subst k; simpa [support] using neg_neg_of_pos hi
      · have hkj : k = j := by
          by_contra hkj
          exact h ⟨hki, hkj⟩
        subst k
        simpa [support] using neg_neg_of_pos hj
  | inr k =>
    constructor
    · intro h
      change k = i at h
      subst k
      simpa [support] using hr
    · intro h
      simpa [support] using ho k h

private lemma endpoint_support_zero_iff (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    support l f (endpoint l i j) = 0 ↔ incident f i j := by
  constructor
  · intro he
    by_contra hn
    exact ((endpoint_support l hl f i j hij).2 hn).ne he
  · exact (endpoint_support l hl f i j hij).1

/-- Supporting traces select precisely the vertices whose support values vanish.
The nonzero-weight filter is necessary: zero-weight vertices need not lie on the trace. -/
private lemma zero_trace_hull {I : Type*} (s : Set V) (L : I → V →ₗ[ℝ] ℝ)
    (hs : ∀ p ∈ s, ∀ i, L i p ≤ 0) :
    convexHull ℝ {p ∈ s | ∀ i, L i p = 0} =
      {x ∈ convexHull ℝ s | ∀ i, L i x = 0} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · exact fun p hp => ⟨subset_convexHull ℝ s hp.1, hp.2⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ s) hx.1 hy.1 ha hb hab, ?_⟩
      intro i
      simp [map_add, map_smul, hx.2 i, hy.2 i]
  · rintro x ⟨hx, hzero⟩
    obtain ⟨J, _, w, z, hw, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hx
    have hterm (i : I) (j : J) : w j * L i (z j) = 0 := by
      have hh : ∑ j, w j * L i (z j) = 0 := by
        simpa only [map_sum, map_smul, smul_eq_mul, hzero i] using congrArg (L i) he
      exact (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw j) (hs (z j) (hz j) i))).mp hh
          j (Finset.mem_univ j)
    let t : Finset J := Finset.univ.filter fun j => w j ≠ 0
    have ht_sum : ∑ j ∈ t, w j = 1 := by
      rw [show (∑ j ∈ t, w j) = ∑ j, w j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        by_contra hjw
        exact hjt (Finset.mem_filter.mpr ⟨hj, hjw⟩)]
      exact hsum
    have ht_vec : ∑ j ∈ t, w j • z j = x := by
      rw [show (∑ j ∈ t, w j • z j) = ∑ j, w j • z j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        have hjw : w j = 0 := by
          by_contra hn
          exact hjt (Finset.mem_filter.mpr ⟨hj, hn⟩)
        simp [hjw]]
      exact he
    rw [← ht_vec]
    exact (convex_convexHull ℝ _).sum_mem
      (fun j _ => hw j) ht_sum (fun j hj => subset_convexHull ℝ _
        ⟨hz j, fun i => (mul_eq_zero.mp (hterm i j)).resolve_left
          (Finset.mem_filter.mp hj).2⟩)

private lemma convex_body (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) :
    Convex ℝ (cutBody l) := by
  rw [← (cut_body_polytope l hl).2.1]
  exact convex_convexHull ℝ _

/-- The two original supports triangularize each four-point affine relation. -/
private lemma independent_of_two_supports (v : Fin 4 → V)
    (L M : V →ₗ[ℝ] ℝ) (hL0 : L (v 0) ≠ 0)
    (hL : ∀ j : Fin 3, L (v j.succ) = 0)
    (hM1 : M (v 1) ≠ 0) (hM2 : M (v 2) = 0) (hM3 : M (v 3) = 0)
    (h23 : v 2 ≠ v 3) : AffineIndependent ℝ v := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw he j
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at he
  have h0 : w 0 = 0 := by
    have hh := congrArg L he
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, Fin.sum_univ_succ] at hh
    have h1 := hL 0
    have h2 := hL 1
    have h3 := hL 2
    change L (v 1) = 0 at h1
    change L (v 2) = 0 at h2
    change L (v 3) = 0 at h3
    simp only [h1, h2, h3, mul_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hL0
  have h1 : w 1 = 0 := by
    have hh := congrArg M he
    simp only [map_sum, map_smul, map_zero, smul_eq_mul, Fin.sum_univ_succ,
      h0, hM2, hM3, zero_mul, mul_zero, zero_add, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_right hM1
  have h3 : w 3 = -w 2 := by
    simp only [Fin.sum_univ_succ, h0, h1] at hw
    linarith
  have hz : w 2 • (v 2 - v 3) = 0 := by
    simpa only [Fin.sum_univ_succ, h0, h1, h3, zero_smul, zero_add,
      add_zero, neg_smul, smul_sub, sub_eq_add_neg] using he
  have h2 : w 2 = 0 := (smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr h23)
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · simpa [h2] using h3

/-- In the sum-one hyperplane, a four-point affine-independent family spans the
whole hyperplane. The proof reconstructs every point using its linear basis. -/
private lemma span_sumOne (v : Fin 4 → V) (hv : ∀ j, v j ∈ sumOne)
    (hi : AffineIndependent ℝ v) : affineSpan ℝ (range v) = sumOne := by
  classical
  have hlin : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have hsum : ∑ j, w j = 0 := by
      have he := congrArg (fun x : V => ∑ i, x i) hw
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
      rw [Finset.sum_comm] at he
      simp only [← Finset.mul_sum, show ∀ j, ∑ i, v j i = 1 from hv, mul_one] at he
      simpa using he
    exact fun j => hi.eq_zero_of_sum_eq_zero hsum hw j (Finset.mem_univ j)
  let B : Basis (Fin 4) ℝ V := basisOfPiSpaceOfLinearIndependent hlin
  have hB (i : Fin 4) : B i = v i := by simp [B]
  apply le_antisymm
  · exact affineSpan_le.mpr (by rintro x ⟨j, rfl⟩; exact hv j)
  · intro x hx
    let w : Fin 4 → ℝ := fun j => B.repr x j
    have he : ∑ j, w j • v j = x := by
      simpa only [hB, w] using B.sum_repr x
    have hw : ∑ j, w j = 1 := by
      have hh := congrArg (fun y : V => ∑ i, y i) he
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [Finset.sum_comm] at hh
      simp only [← Finset.mul_sum, show ∀ j, ∑ i, v j i = 1 from hv, mul_one] at hh
      exact hh.trans hx
    have hm := affineCombination_mem_affineSpan hw v
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, he] at hm
    exact hm

private lemma linear_nonpos_on_hull (s : Set V) (L : V →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ s, L x ≤ 0) : ∀ x ∈ convexHull ℝ s, L x ≤ 0 := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
    (mul_nonpos_of_nonneg_of_nonpos hb hy)

/-- Strictness is obtained in the actual intrinsic interior by an extension
inside its affine span; ambient four-dimensional interiors never enter. -/
private lemma separate_intrinsic (s t : Set V) (L : V →ₗ[ℝ] ℝ)
    (hs : ∀ x ∈ s, L x ≤ 0) (ht : ∀ x ∈ t, 0 ≤ L x)
    (hw : ∃ y ∈ s, L y < 0) :
    Disjoint (intrinsicInterior ℝ s) (intrinsicInterior ℝ t) := by
  rw [Set.disjoint_left]
  intro x hx hxt
  have hxs := intrinsicInterior_subset hx
  have hxts := intrinsicInterior_subset hxt
  have hz : L x = 0 := le_antisymm (hs x hxs) (ht x hxts)
  obtain ⟨y, hy, hly⟩ := hw
  obtain ⟨a, ha, he⟩ :=
    D5.S3.Geometry.Gluing.BarycentricSubdivisionStar.intrinsic_extension_for_subdivision s x y hx hy
  have hn := hs _ he
  simp only [map_add, map_smul, map_sub, smul_eq_mul, hz, zero_sub, zero_add] at hn
  exact (not_lt_of_ge hn) (mul_pos ha (neg_pos.mpr hly))

private lemma vertex_geometry (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (n : Fin 20) :
    (∀ j, vertices l n j ∈ cutBody l) ∧
    (∀ j : Fin 3, support l (facet n) (vertices l n j.succ) = 0) ∧
    support l (ridge n) (vertices l n 1) < 0 ∧
    support l (ridge n) (vertices l n 2) = 0 ∧
    support l (ridge n) (vertices l n 3) = 0 ∧
    vertices l n 2 ≠ vertices l n 3 := by
  have hp (i j : Fin 4) (hij : i ≠ j) : endpoint l i j ∈ cutBody l :=
    ((cut_body_polytope l hl).2.2.2 i j hij).1
  have hb : barycenter ∈ cutBody l := (shared_radial_body l hl).2.1
  have hn (i j a b : Fin 4) (hij : i ≠ j) (hab : a ≠ b)
      (hne : (i,j) ≠ (a,b)) : endpoint l i j ≠ endpoint l a b := by
    intro he
    exact hne (congrArg Subtype.val ((cut_body_polytope l hl).2.2.1
      (a₁ := (⟨(i,j), hij⟩ : EndpointLabel)) (a₂ := ⟨(a,b), hab⟩) he))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases n <;> fin_cases j <;> simp only [vertices]
    all_goals first | exact hb | exact hp _ _ (by decide)
  · intro j
    fin_cases n <;> fin_cases j <;> simp only [vertices, facet]
    all_goals exact (endpoint_support l hl _ _ _ (by decide)).1 (by decide)
  · fin_cases n <;> simp only [vertices, ridge]
    all_goals exact (endpoint_support l hl _ _ _ (by decide)).2 (by decide)
  · fin_cases n <;> simp only [vertices, ridge]
    all_goals exact (endpoint_support l hl _ _ _ (by decide)).1 (by decide)
  · fin_cases n <;> simp only [vertices, ridge]
    all_goals exact (endpoint_support l hl _ _ _ (by decide)).1 (by decide)
  · fin_cases n <;> simp only [vertices]
    all_goals exact hn _ _ _ _ (by decide) (by decide) (by decide)

/-- Exact cap hulls, derived from the twelve original extreme endpoints. -/
private lemma cap_triangle (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (i : Fin 4) :
    {x ∈ cutBody l | support l (Sum.inr i) x = 0} =
      boundaryTriangle l (capIndex i) := by
  let P : Set V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  have hP : convexHull ℝ P = cutBody l := (cut_body_polytope l hl).2.1
  have hz := zero_trace_hull P (fun _ : Unit => support l (Sum.inr i))
    (by rintro p ⟨⟨⟨a,b⟩,hab⟩,rfl⟩ _
        exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 _)
  have hverts : {p ∈ P | support l (Sum.inr i) p = 0} =
      range (fun j : Fin 3 => vertices l (capIndex i) j.succ) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟨a,b⟩,hab⟩,rfl⟩,h⟩
      have hi := (endpoint_support_zero_iff l hl (Sum.inr i) a b hab).mp h
      change i = a at hi
      subst a
      fin_cases i <;> fin_cases b <;>
        simp_all [vertices, capIndex, Set.mem_range, Fin.exists_fin_succ]
    · rintro ⟨j,rfl⟩
      refine ⟨?_, ?_⟩
      · fin_cases i <;> fin_cases j
        all_goals refine ⟨⟨(_, _), ?_⟩, rfl⟩ <;> decide
      · have hf : facet (capIndex i) = Sum.inr i := by fin_cases i <;> rfl
        simpa only [hf] using (vertex_geometry l hl (capIndex i)).2.1 j
  simpa only [hP, forall_const, hverts, boundaryTriangle] using hz.symm

/-- All six cyclic supporting traces are exactly the original closed edge segments. -/
private lemma cycle_edge_hull (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4) (r : Fin 6) :
    {x ∈ cutBody l | support l (Sum.inl k) x = 0 ∧
      support l (cycleSupport k r) x = 0} =
    segment ℝ (sideCycle l k r) (sideCycle l k (r + 1)) := by
  let P : Set V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  have hP : convexHull ℝ P = cutBody l := (cut_body_polytope l hl).2.1
  let L : Fin 2 → V →ₗ[ℝ] ℝ :=
    ![support l (Sum.inl k), support l (cycleSupport k r)]
  have hz := zero_trace_hull P L
    (by rintro p ⟨⟨⟨a,b⟩,hab⟩,rfl⟩ j
        fin_cases j <;> exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 _)
  have hverts : {p ∈ P | ∀ j, L j p = 0} =
      {sideCycle l k r, sideCycle l k (r + 1)} := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟨a,b⟩,hab⟩,rfl⟩,h⟩
      have h0 := (endpoint_support_zero_iff l hl (Sum.inl k) a b hab).mp (h 0)
      have h1 := (endpoint_support_zero_iff l hl (cycleSupport k r) a b hab).mp (h 1)
      fin_cases k <;> fin_cases r <;> fin_cases a <;> fin_cases b <;>
        simp_all [incident, cycleSupport, sideCycle, sideOrder]
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      all_goals
        refine ⟨?_, ?_⟩
        · fin_cases k <;> fin_cases r
          all_goals refine ⟨⟨(_, _), ?_⟩, rfl⟩ <;> decide
        · intro j
          fin_cases k <;> fin_cases r <;> fin_cases j <;>
            simp only [L, cycleSupport, sideCycle, sideOrder]
          all_goals exact (endpoint_support l hl _ _ _ (by decide)).1 (by decide)
  have hbody : {x ∈ convexHull ℝ P | ∀ j, L j x = 0} =
      {x ∈ cutBody l | support l (Sum.inl k) x = 0 ∧
        support l (cycleSupport k r) x = 0} := by
    simp [hP, L, Fin.forall_fin_succ]
  rw [hverts, hbody, convexHull_pair] at hz
  exact hz.symm

/-- The four opposite edges used by the fan, supplied by the complete cyclic trace theorem. -/
private lemma side_edge (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k r : Fin 4) :
    {x ∈ cutBody l | support l (Sum.inl k) x = 0 ∧
      support l (ridge (sideIndex k r)) x = 0} =
    segment ℝ (vertices l (sideIndex k r) 2) (vertices l (sideIndex k r) 3) := by
  have h := cycle_edge_hull l hl k (⟨r.val + 1, by omega⟩ : Fin 6)
  fin_cases k <;> fin_cases r <;>
    simpa [cycleSupport, sideCycle, sideOrder, ridge, sideIndex, vertices] using h

private lemma cone_triangle_mem (l : Fin 6 → ℝ) (n : Fin 20) (x y : V)
    (hy : y ∈ segment ℝ (vertices l n 2) (vertices l n 3))
    (hx : x ∈ segment ℝ (vertices l n 1) y) : x ∈ boundaryTriangle l n := by
  have hr : range (fun j : Fin 3 => vertices l n j.succ) =
      {vertices l n 1, vertices l n 2, vertices l n 3} := by
    ext z
    simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
  rw [boundaryTriangle, hr, ← convexJoin_singleton_segment]
  exact mem_convexJoin.mpr ⟨vertices l n 1, rfl, y, hy, hx⟩

/-- The actual four-triangle fan cover of each original side. -/
private lemma side_cover_point (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (k : Fin 4) (x : V) (hx : x ∈ cutBody l) (hxk : x k = 0) :
    ∃ r : Fin 4, x ∈ boundaryTriangle l (sideIndex k r) := by
  let σ := sideOrder k
  let a := sideCycle l k 0
  have hσ0 : σ 0 = k := by fin_cases k <;> rfl
  have ha (r : Fin 4) : vertices l (sideIndex k r) 1 = a := by
    fin_cases k <;> fin_cases r <;> rfl
  by_cases hxa : x = a
  · refine ⟨0, ?_⟩
    rw [hxa, ← ha 0]
    exact subset_convexHull ℝ _ ⟨0, rfl⟩
  obtain ⟨t, ht, ht1, hy, hyk, htrace, he⟩ :=
    side_fan_ray_exit l hl σ x hx (by simpa only [hσ0] using hxk) hxa
  let y : V := fun s => a s + (x s - a s) / t
  have hy' : y ∈ cutBody l := hy
  have hyk' : support l (Sum.inl k) y = 0 := by
    change -y k = 0
    rw [← hσ0]
    simpa only [neg_eq_zero] using hyk
  have hxy (r : Fin 4) : x ∈ segment ℝ (vertices l (sideIndex k r) 1) y := by
    rw [ha]
    exact ⟨1-t, t, by linarith, ht.le, by ring, he.symm⟩
  have hfinish (r : Fin 4) (hr : support l (ridge (sideIndex k r)) y = 0) :
      x ∈ boundaryTriangle l (sideIndex k r) := by
    apply cone_triangle_mem l _ x y
    · rw [← side_edge l hl k r]
      exact ⟨hy', hyk', hr⟩
    · exact hxy r
  rcases htrace with h | h | h | h
  · refine ⟨0, hfinish 0 ?_⟩
    fin_cases k <;> simpa [support, ridge, sideIndex, σ, sideOrder] using h
  · refine ⟨1, hfinish 1 ?_⟩
    fin_cases k <;> simpa [support, ridge, sideIndex, σ, sideOrder] using congrArg Neg.neg h
  · refine ⟨2, hfinish 2 ?_⟩
    fin_cases k <;> simpa [support, ridge, sideIndex, σ, sideOrder] using h
  · refine ⟨3, hfinish 3 ?_⟩
    fin_cases k <;> simpa [support, ridge, sideIndex, σ, sideOrder] using congrArg Neg.neg h

/-- Equality with the complete original closed side, including the fan diagonals
and all six boundary edges. -/
private lemma side_cover (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4) :
    {x ∈ cutBody l | x k = 0} = ⋃ r : Fin 4, boundaryTriangle l (sideIndex k r) := by
  apply Subset.antisymm
  · rintro x ⟨hx,hk⟩
    obtain ⟨r,hr⟩ := side_cover_point l hl k x hx hk
    exact Set.mem_iUnion.mpr ⟨r,hr⟩
  · apply Set.iUnion_subset
    intro r
    apply convexHull_min
    · rintro x ⟨j,rfl⟩
      have hg := vertex_geometry l hl (sideIndex k r)
      refine ⟨hg.1 _, ?_⟩
      have h := hg.2.1 j
      have hf : facet (sideIndex k r) = Sum.inl k := by
        fin_cases k <;> fin_cases r <;> rfl
      rw [hf] at h
      exact neg_eq_zero.mp h
    · apply (convex_body l hl).inter
      intro x hx y hy a b ha hb hab
      change a * x k + b * y k = 0
      rw [hx,hy]
      ring

private lemma cone_cell_mem (l : Fin 6 → ℝ) (n : Fin 20) (x y : V)
    (hy : y ∈ boundaryTriangle l n) (hx : x ∈ segment ℝ barycenter y) :
    x ∈ cell l n := by
  have hb : vertices l n 0 = barycenter := by fin_cases n <;> rfl
  rw [cell, Fin.range_fin_succ, hb, convexHull_insert (range_nonempty _)]
  exact mem_convexJoin.mpr ⟨barycenter, rfl, y, hy, hx⟩

private lemma separate_hulls (v w : Fin 4 → V) (D : V →ₗ[ℝ] ℝ)
    (hv : ∀ j, D (v j) ≤ 0) (hw : ∀ j, 0 ≤ D (w j))
    (hex : ∃ j, D (v j) < 0) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (range v)))
      (intrinsicInterior ℝ (convexHull ℝ (range w))) := by
  apply separate_intrinsic _ _ D
  · exact linear_nonpos_on_hull _ D (by rintro x ⟨j,rfl⟩; exact hv j)
  · have h := linear_nonpos_on_hull (range w) (-D)
      (by rintro x ⟨j,rfl⟩; exact neg_nonpos.mpr (hw j))
    exact fun x hx => neg_nonpos.mp (h x hx)
  · obtain ⟨j,hj⟩ := hex
    exact ⟨v j, subset_convexHull ℝ _ ⟨j,rfl⟩, hj⟩

/-- Cones on different original supporting faces are separated by the difference
of the two normalized supports. No hypothesis of a subdivision is used. -/
private lemma different_facet_disjoint (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (n m : Fin 20) (hnm : facet n ≠ facet m) :
    Disjoint (intrinsicInterior ℝ (cell l n)) (intrinsicInterior ℝ (cell l m)) := by
  let L := support l (facet n)
  let M := support l (facet m)
  let D : V →ₗ[ℝ] ℝ := M barycenter • L - L barycenter • M
  have hLb : L barycenter < 0 := support_barycenter l hl _
  have hMb : M barycenter < 0 := support_barycenter l hl _
  have hn := vertex_geometry l hl n
  have hm := vertex_geometry l hl m
  have hb (q : Fin 20) : vertices l q 0 = barycenter := by fin_cases q <;> rfl
  have hDb : D barycenter = 0 := by simp [D]; ring
  have hnle (j : Fin 4) : D (vertices l n j) ≤ 0 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [hb, hDb]
    · have hzero : L (vertices l n j.succ) = 0 := hn.2.1 j
      have hnonpos : M (vertices l n j.succ) ≤ 0 := support_body l _ (hn.1 _) _
      simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hzero,
        mul_zero, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos hLb.le hnonpos)
  have hmge (j : Fin 4) : 0 ≤ D (vertices l m j) := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [hb, hDb]
    · have hzero : M (vertices l m j.succ) = 0 := hm.2.1 j
      have hnonpos : L (vertices l m j.succ) ≤ 0 := support_body l _ (hm.1 _) _
      simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hzero,
        mul_zero, sub_zero]
      exact mul_nonneg_of_nonpos_of_nonpos hMb.le hnonpos
  have hwitness : ∃ j : Fin 3, M (vertices l n j.succ) < 0 := by
    dsimp only [M]
    fin_cases n <;> fin_cases m
    all_goals first
      | exact (hnm (by rfl)).elim
      | exact ⟨0, (endpoint_support l hl _ _ _ (by decide)).2 (by decide)⟩
      | exact ⟨1, (endpoint_support l hl _ _ _ (by decide)).2 (by decide)⟩
      | exact ⟨2, (endpoint_support l hl _ _ _ (by decide)).2 (by decide)⟩
  apply separate_hulls (vertices l n) (vertices l m) D hnle hmge
  obtain ⟨j,hj⟩ := hwitness
  refine ⟨j.succ, ?_⟩
  have hzero : L (vertices l n j.succ) = 0 := hn.2.1 j
  simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hzero,
    mul_zero, zero_sub]
  exact neg_neg_of_pos (mul_pos_of_neg_of_neg hLb hj)

/-- For triangles on the same original side, subtract the side-coordinate
multiple so that the side separator also vanishes at the common barycenter. -/
private lemma same_side_disjoint (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (k r s : Fin 4) (hrs : r ≠ s) :
    Disjoint (intrinsicInterior ℝ (cell l (sideIndex k r)))
      (intrinsicInterior ℝ (cell l (sideIndex k s))) := by
  let n := sideIndex k r
  let m := sideIndex k s
  let a := endpoint l ((sideOrder k) 1) ((sideOrder k) 2)
  let L := support l (ridge n)
  let M := support l (ridge m)
  let D₀ : V →ₗ[ℝ] ℝ := M a • L - L a • M
  let D : V →ₗ[ℝ] ℝ := D₀ - (4 * D₀ barycenter) • LinearMap.proj k
  have hb (q : Fin 20) : vertices l q 0 = barycenter := by fin_cases q <;> rfl
  have ha (u : Fin 4) : vertices l (sideIndex k u) 1 = a := by
    fin_cases k <;> fin_cases u <;> rfl
  have hk (u : Fin 4) (j : Fin 3) : vertices l (sideIndex k u) j.succ k = 0 := by
    have h := (vertex_geometry l hl (sideIndex k u)).2.1 j
    have hf : facet (sideIndex k u) = Sum.inl k := by fin_cases k <;> fin_cases u <;> rfl
    rw [hf] at h
    exact neg_eq_zero.mp h
  have hD (u : Fin 4) (j : Fin 3) :
      D (vertices l (sideIndex k u) j.succ) = D₀ (vertices l (sideIndex k u) j.succ) := by
    simp [D, hk]
  have hDb : D barycenter = 0 := by simp [D, barycenter]; ring
  have hDa : D₀ a = 0 := by simp [D₀]; ring
  have hn := vertex_geometry l hl n
  have hm := vertex_geometry l hl m
  have hLa : L a < 0 := by simpa only [n, ha] using hn.2.2.1
  have hMa : M a < 0 := by simpa only [m, ha] using hm.2.2.1
  have hnle (j : Fin 4) : D (vertices l n j) ≤ 0 := by
    fin_cases j
    · change D (vertices l n 0) ≤ 0
      rw [hb, hDb]
    · change D (vertices l n 1) ≤ 0
      have ha0 : vertices l (sideIndex k r) (0 : Fin 3).succ = a := by simpa using ha r
      rw [show vertices l n 1 = vertices l (sideIndex k r) (0 : Fin 3).succ from rfl,
        hD r 0, ha0, hDa]
    · change D (vertices l n 2) ≤ 0
      rw [show vertices l n 2 = vertices l (sideIndex k r) (1 : Fin 3).succ from rfl,
        hD r 1]
      have hz : L (vertices l n 2) = 0 := hn.2.2.2.1
      have hnM : M (vertices l n 2) ≤ 0 := support_body l _ (hn.1 2) _
      change M a * L (vertices l n 2) - L a * M (vertices l n 2) ≤ 0
      rw [hz, mul_zero, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos hLa.le hnM)
    · change D (vertices l n 3) ≤ 0
      rw [show vertices l n 3 = vertices l (sideIndex k r) (2 : Fin 3).succ from rfl,
        hD r 2]
      have hz : L (vertices l n 3) = 0 := hn.2.2.2.2.1
      have hnM : M (vertices l n 3) ≤ 0 := support_body l _ (hn.1 3) _
      change M a * L (vertices l n 3) - L a * M (vertices l n 3) ≤ 0
      rw [hz, mul_zero, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos hLa.le hnM)
  have hmge (j : Fin 4) : 0 ≤ D (vertices l m j) := by
    fin_cases j
    · change 0 ≤ D (vertices l m 0)
      rw [hb, hDb]
    · change 0 ≤ D (vertices l m 1)
      have ha0 : vertices l (sideIndex k s) (0 : Fin 3).succ = a := by simpa using ha s
      rw [show vertices l m 1 = vertices l (sideIndex k s) (0 : Fin 3).succ from rfl,
        hD s 0, ha0, hDa]
    · change 0 ≤ D (vertices l m 2)
      rw [show vertices l m 2 = vertices l (sideIndex k s) (1 : Fin 3).succ from rfl,
        hD s 1]
      have hz : M (vertices l m 2) = 0 := hm.2.2.2.1
      have hnL : L (vertices l m 2) ≤ 0 := support_body l _ (hm.1 2) _
      change 0 ≤ M a * L (vertices l m 2) - L a * M (vertices l m 2)
      rw [hz, mul_zero, sub_zero]
      exact mul_nonneg_of_nonpos_of_nonpos hMa.le hnL
    · change 0 ≤ D (vertices l m 3)
      rw [show vertices l m 3 = vertices l (sideIndex k s) (2 : Fin 3).succ from rfl,
        hD s 2]
      have hz : M (vertices l m 3) = 0 := hm.2.2.2.2.1
      have hnL : L (vertices l m 3) ≤ 0 := support_body l _ (hm.1 3) _
      change 0 ≤ M a * L (vertices l m 3) - L a * M (vertices l m 3)
      rw [hz, mul_zero, sub_zero]
      exact mul_nonneg_of_nonpos_of_nonpos hMa.le hnL
  have hwitness : M (vertices l n 2) < 0 ∨ M (vertices l n 3) < 0 := by
    dsimp only [M, n, m]
    fin_cases k <;> fin_cases r <;> fin_cases s
    all_goals first
      | exact (hrs rfl).elim
      | exact Or.inl ((endpoint_support l hl _ _ _ (by decide)).2 (by decide))
      | exact Or.inr ((endpoint_support l hl _ _ _ (by decide)).2 (by decide))
  apply separate_hulls (vertices l n) (vertices l m) D hnle hmge
  rcases hwitness with h | h
  · refine ⟨2, ?_⟩
    rw [show vertices l n 2 = vertices l (sideIndex k r) (1 : Fin 3).succ from rfl, hD]
    have hz : L (vertices l n 2) = 0 := hn.2.2.2.1
    change M a * L (vertices l n 2) - L a * M (vertices l n 2) < 0
    rw [hz, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos_of_neg_of_neg hLa h)
  · refine ⟨3, ?_⟩
    rw [show vertices l n 3 = vertices l (sideIndex k r) (2 : Fin 3).succ from rfl, hD]
    have hz : L (vertices l n 3) = 0 := hn.2.2.2.2.1
    change M a * L (vertices l n 3) - L a * M (vertices l n 3) < 0
    rw [hz, mul_zero, zero_sub]
    exact neg_neg_of_pos (mul_pos_of_neg_of_neg hLa h)

/-- The full literal closed subdivision. The last two clauses explicitly identify
and separate the interiors in the single sum-one affine hyperplane. -/
theorem twenty_subdivision (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) :
    cutBody l = (⋃ n : Fin 20, cell l n) ∧
    (∀ n : Fin 20, IsClosed (cell l n) ∧ AffineIndependent ℝ (vertices l n) ∧
      affineSpan ℝ (range (vertices l n)) = sumOne ∧ affineSpan ℝ (cell l n) = sumOne) ∧
    (∀ n : Fin 20, intrinsicInterior ℝ (cell l n) =
      Subtype.val '' interior (Subtype.val ⁻¹' cell l n : Set sumOne)) ∧
    Pairwise (fun n m : Fin 20 =>
      Disjoint (intrinsicInterior ℝ (cell l n)) (intrinsicInterior ℝ (cell l m))) ∧
    Pairwise (fun n m : Fin 20 =>
      Disjoint (interior (Subtype.val ⁻¹' cell l n : Set sumOne))
        (interior (Subtype.val ⁻¹' cell l m : Set sumOne))) := by
  classical
  have hsubset (n : Fin 20) : cell l n ⊆ cutBody l :=
    convexHull_min (by rintro x ⟨j,rfl⟩; exact (vertex_geometry l hl n).1 j)
      (convex_body l hl)
  have hcover : cutBody l = ⋃ n : Fin 20, cell l n := by
    apply Subset.antisymm
    · intro x hx
      by_cases hb : x = barycenter
      · apply Set.mem_iUnion.mpr
        refine ⟨0, ?_⟩
        rw [hb]
        exact subset_convexHull ℝ _ ⟨0, rfl⟩
      obtain ⟨t, ht, ht1, hy, htrace, he⟩ := barycenter_ray_exit l hl x hx hb
      let y : V := fun j => 1 / 4 + (x j - 1 / 4) / t
      have hxy : x ∈ segment ℝ barycenter y :=
        ⟨1-t,t,by linarith,ht.le,by ring,he.symm⟩
      rcases htrace with ⟨k,hk⟩ | ⟨i,hi⟩
      · have hs : y ∈ ⋃ r : Fin 4, boundaryTriangle l (sideIndex k r) := by
          rw [← side_cover l hl k]
          exact ⟨hy,hk⟩
        obtain ⟨r,hr⟩ := Set.mem_iUnion.mp hs
        exact Set.mem_iUnion.mpr ⟨sideIndex k r, cone_cell_mem l _ x y hr hxy⟩
      · have hi' : support l (Sum.inr i) y = 0 := by simpa [y, support] using hi
        have hymem : y ∈ boundaryTriangle l (capIndex i) := by
          rw [← cap_triangle l hl i]
          exact ⟨hy,hi'⟩
        exact Set.mem_iUnion.mpr ⟨capIndex i, cone_cell_mem l _ x y hymem hxy⟩
    · exact Set.iUnion_subset hsubset
  have hgeom (n : Fin 20) : IsClosed (cell l n) ∧ AffineIndependent ℝ (vertices l n) ∧
      affineSpan ℝ (range (vertices l n)) = sumOne ∧ affineSpan ℝ (cell l n) = sumOne := by
    obtain ⟨hv,hf,hg,hg2,hg3,hne⟩ := vertex_geometry l hl n
    have hb : vertices l n 0 = barycenter := by fin_cases n <;> rfl
    have hi := independent_of_two_supports (vertices l n)
      (support l (facet n)) (support l (ridge n))
      (by rw [hb]; exact (support_barycenter l hl _).ne) hf hg.ne hg2 hg3 hne
    have hs := span_sumOne (vertices l n) (fun j => (hv j).1.2) hi
    refine ⟨(Set.finite_range _).isClosed_convexHull ℝ, hi, hs, ?_⟩
    simpa only [cell, affineSpan_convexHull] using hs
  have hinterior (n : Fin 20) : intrinsicInterior ℝ (cell l n) =
      Subtype.val '' interior (Subtype.val ⁻¹' cell l n : Set sumOne) := by
    unfold intrinsicInterior
    rw [(hgeom n).2.2.2]
  have hdisjoint : Pairwise (fun n m : Fin 20 =>
      Disjoint (intrinsicInterior ℝ (cell l n)) (intrinsicInterior ℝ (cell l m))) := by
    intro n m hnm
    by_cases hf : facet n = facet m
    · have hcap (i : Fin 4) : facet (capIndex i) = Sum.inr i := by
        fin_cases i <;> rfl
      have hside (k r : Fin 4) : facet (sideIndex k r) = Sum.inl k := by
        fin_cases k <;> fin_cases r <;> rfl
      have hclass (q : Fin 20) : (∃ i : Fin 4, q = capIndex i) ∨
          ∃ k r : Fin 4, q = sideIndex k r := by
        fin_cases q
        · exact Or.inl ⟨0, rfl⟩
        · exact Or.inl ⟨1, rfl⟩
        · exact Or.inl ⟨2, rfl⟩
        · exact Or.inl ⟨3, rfl⟩
        · exact Or.inr ⟨0, 0, rfl⟩
        · exact Or.inr ⟨0, 1, rfl⟩
        · exact Or.inr ⟨0, 2, rfl⟩
        · exact Or.inr ⟨0, 3, rfl⟩
        · exact Or.inr ⟨1, 0, rfl⟩
        · exact Or.inr ⟨1, 1, rfl⟩
        · exact Or.inr ⟨1, 2, rfl⟩
        · exact Or.inr ⟨1, 3, rfl⟩
        · exact Or.inr ⟨2, 0, rfl⟩
        · exact Or.inr ⟨2, 1, rfl⟩
        · exact Or.inr ⟨2, 2, rfl⟩
        · exact Or.inr ⟨2, 3, rfl⟩
        · exact Or.inr ⟨3, 0, rfl⟩
        · exact Or.inr ⟨3, 1, rfl⟩
        · exact Or.inr ⟨3, 2, rfl⟩
        · exact Or.inr ⟨3, 3, rfl⟩
      rcases hclass n with ⟨i,rfl⟩ | ⟨k,r,rfl⟩
      · rcases hclass m with ⟨j,rfl⟩ | ⟨h,s,rfl⟩
        · rw [hcap, hcap] at hf
          have hij : i = j := Sum.inr.inj hf
          exact (hnm (congrArg capIndex hij)).elim
        · rw [hcap, hside] at hf
          cases hf
      · rcases hclass m with ⟨i,rfl⟩ | ⟨h,s,rfl⟩
        · rw [hside, hcap] at hf
          cases hf
        · rw [hside, hside] at hf
          have hkh : k = h := Sum.inl.inj hf
          subst h
          exact same_side_disjoint l hl k r s (fun hrs => hnm (congrArg (sideIndex k) hrs))
    · exact different_facet_disjoint l hl n m hf
  refine ⟨hcover, hgeom, hinterior, hdisjoint, ?_⟩
  intro n m hnm
  rw [Set.disjoint_left]
  intro x hx hy
  have hx' : (x : V) ∈ intrinsicInterior ℝ (cell l n) := by
    rw [hinterior]
    exact ⟨x,hx,rfl⟩
  have hy' : (x : V) ∈ intrinsicInterior ℝ (cell l m) := by
    rw [hinterior]
    exact ⟨x,hy,rfl⟩
  exact Set.disjoint_left.mp (hdisjoint hnm) hx' hy'

end D5.S3.Geometry.Hyperideal.LengthGramTwentySubdivision
