/- GID: D5/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/UlfarssonAlternatingMeshBasis
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The mesh-pattern basis of the even permutations is fully shaded and odd. -/

/-
proof_shape: result: content (two-point insertion and full-shading rigidity).
escape_witness: none (the module uses the external open-problem resolution basis).
admission_basis: open-problem-resolution (#19120; Proved)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19180.
Private auxiliary classifications (consumers follow the colon):
  skipTwo_val: bind-only; skipTwo_lt_gap, skipTwo_ne_gap.
  skipTwo_lt_gap: bind-only; count_gap_positions, count_gap_values.
  count_gap_positions, count_gap_values: bind-only; occurs_insertPair.
  skipTwo_ne_gap: bind-only; insertPair_swap.
  placeTwo_inl: bind-only; insertPair_selected, not_range_skipTwo, insertPair_swap.
  placeTwo_inr: bind-only; insertPair_gap, not_range_skipTwo, insertPair_swap.
  insertPair_selected: bind-only; count_gap_values, occurs_insertPair, insertPair_swap.
  insertPair_gap: bind-only; count_gap_values, insertPair_swap.
  not_range_skipTwo: bind-only; occurs_insertPair.
  occurs_insertPair: content (an explicit occurrence); exists_even_extension.
  insertPair_swap: bind-only; insertPair_sign_flip.
  insertPair_sign_flip: bind-only; exists_even_extension.
  exists_even_extension: content (a parity-selected extension); result.
  occurs_self: bind-only; full_occurs_iff, result.
  full_occurs_iff: content (surjectivity forced by shading); result.
  mesh_ext: bind-only; result.
The public definitions use the expressions of issue #19120, including length zero.
The proof of result uses only the avoidance equality in IsBasis.
All declarations are general constructions or theorems, not bounded enumeration,
a checker, a numeric reduction, or a certified finite instance (utility: none).
-/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

/-! Mesh patterns in H. Ulfarsson, "BiSC: An algorithm for discovering generalized permutation
patterns", arXiv:2411.17778v1, Section 2 (mesh patterns, avoidance, bases) and Conjecture 2.4.2. -/

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

/-- A mesh pattern `(p, R)`: a permutation `p ∈ S_k` and a shading `R ⊆ {0, …, k} × {0, …, k}`. -/
structure MeshPattern where
  k : ℕ
  p : Equiv.Perm (Fin k)
  R : Set (Fin (k + 1) × Fin (k + 1))

/-- An occurrence of `(p, R)` in `σ ∈ S_n` (Brändén–Claesson mesh patterns, as used in Section 2):
selected positions `e` (increasing) whose values are order-isomorphic to `p`, such that no unselected point
of `σ` lies in a shaded cell. The cell of an unselected point `x` is `(i, j)` with `i` the number of
selected positions left of `x` and `j` the number of selected values below `σ x`. -/
def Occurs (P : MeshPattern) {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ e : Fin P.k ↪o Fin n,
    (∀ i j : Fin P.k, σ (e i) < σ (e j) ↔ P.p i < P.p j) ∧
    ∀ x : Fin n, x ∉ Set.range e → ∀ c ∈ P.R,
      ¬ (c.1.val = (Finset.univ.filter fun i : Fin P.k => e i < x).card ∧
          c.2.val = (Finset.univ.filter fun i : Fin P.k => σ (e i) < σ x).card)

/-- `Av(P)`: the permutations (of every length) avoiding every pattern in `P`. -/
def Av (P : Set MeshPattern) : Set (Σ n : ℕ, Equiv.Perm (Fin n)) :=
  {σ | ∀ q ∈ P, ¬ Occurs q σ.2}

/-- Section 2: `P` is a basis for `A` if `A = Av(P)` and no subset of `P` has this property. -/
def IsBasis (A : Set (Σ n : ℕ, Equiv.Perm (Fin n))) (P : Set MeshPattern) : Prop :=
  Av P = A ∧ ∀ Q ⊆ P, Av Q = A → Q = P

/-- The union of the alternating subgroups: the even permutations of every length. -/
def Alt : Set (Σ n : ℕ, Equiv.Perm (Fin n)) :=
  {σ | Equiv.Perm.sign σ.2 = 1}

/-- Conjecture 2.4.2: "Let `A` be the union of the alternating subgroups, and let `P` be a basis of patterns
such that `A = Av(P)`. Then `P = {(p, {0,…,n} × {0,…,n}) : p ∈ S_n ∖ A for some n}`." -/
def claim : Prop :=
  ∀ P : Set MeshPattern, IsBasis Alt P →
    P = {q | q.R = Set.univ ∧ Equiv.Perm.sign q.p ≠ 1}

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

/-- The original points skip the two slots of a cell. -/
private def skipTwo {k : ℕ} (a : Fin (k + 1)) : Fin k ↪o Fin (k + 2) :=
  (Fin.succAboveOrderEmb a).trans (Fin.succAboveOrderEmb a.castSucc)

private lemma skipTwo_val {k : ℕ} (a : Fin (k + 1)) (i : Fin k) :
    (skipTwo a i).val = if i.val < a.val then i.val else i.val + 2 := by
  change (a.castSucc.succAbove (a.succAbove i)).val = _
  by_cases h : i.castSucc < a
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    rw [Fin.succAbove_of_castSucc_lt a.castSucc i.castSucc
      (show i.castSucc.castSucc < a.castSucc from h)]
    rw [ite_eq_left (show i.val < a.val from h)]
    rfl
  · have ha : a ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ ha]
    rw [Fin.succAbove_of_le_castSucc _ _ (by change a.val ≤ i.val + 1; exact le_trans ha (Nat.le_succ _))]
    simp only [Fin.val_succ]
    rw [ite_eq_right (show ¬ i.val < a.val from h)]

private def gapPoint {k : ℕ} (a : Fin (k + 1)) (t : Fin 2) : Fin (k + 2) :=
  Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ a.isLt) 2) (Fin.natAdd a.val t)

private lemma skipTwo_lt_gap {k : ℕ} (a : Fin (k + 1)) (i : Fin k) (t : Fin 2) :
    skipTwo a i < gapPoint a t ↔ i.val < a.val := by
  change (skipTwo a i).val < a.val + t.val ↔ _
  rw [skipTwo_val]
  have := t.isLt
  split_ifs <;> omega

private lemma skipTwo_ne_gap {k : ℕ} (a : Fin (k + 1)) (i : Fin k) (t : Fin 2) :
    skipTwo a i ≠ gapPoint a t := by
  intro h
  have h' := congrArg Fin.val h
  change (skipTwo a i).val = a.val + t.val at h'
  rw [skipTwo_val] at h'
  have := t.isLt
  split_ifs at h' <;> omega

private def placeTwo {k : ℕ} (a : Fin (k + 1)) : Fin k ⊕ Fin 2 ≃ Fin (k + 2) :=
  finSumFinEquiv.trans
    ((finSuccEquiv' (Fin.last k).castSucc).trans
      ((Equiv.optionCongr (finSuccEquiv' (Fin.last k))).trans
        ((Equiv.optionCongr (finSuccEquiv' a).symm).trans
          (finSuccEquiv' a.castSucc).symm)))

@[simp] private lemma placeTwo_inl {k : ℕ} (a : Fin (k + 1)) (i : Fin k) :
    placeTwo a (Sum.inl i) = skipTwo a i := by
  have h : (finSuccEquiv' (Fin.last k).castSucc) (Fin.castAdd 2 i) = some i.castSucc :=
    finSuccEquiv'_below (show i.castSucc.castSucc < (Fin.last k).castSucc from i.isLt)
  simp only [placeTwo, Equiv.trans_apply, finSumFinEquiv_apply_left, h,
    Equiv.optionCongr_apply, Option.map_some, finSuccEquiv'_last_apply_castSucc,
    finSuccEquiv'_symm_some, skipTwo]
  rfl

@[simp] private lemma placeTwo_inr {k : ℕ} (a : Fin (k + 1)) (t : Fin 2) :
    placeTwo a (Sum.inr t) = gapPoint a t := by
  apply Fin.ext
  fin_cases t
  · change ((finSuccEquiv' a.castSucc).symm
      (Option.map (finSuccEquiv' a).symm
        (Option.map (finSuccEquiv' (Fin.last k))
          ((finSuccEquiv' (Fin.last k).castSucc) (Fin.last k).castSucc)))).val = a.val
    simp only [finSuccEquiv'_at, Option.map_none, finSuccEquiv'_symm_none, Fin.val_castSucc]
  · change ((finSuccEquiv' a.castSucc).symm
      (Option.map (finSuccEquiv' a).symm
        (Option.map (finSuccEquiv' (Fin.last k))
          ((finSuccEquiv' (Fin.last k).castSucc) (Fin.last k).succ)))).val = a.val + 1
    rw [finSuccEquiv'_above (le_refl _)]
    simp only [Option.map_some, finSuccEquiv'_at, finSuccEquiv'_symm_none,
      finSuccEquiv'_symm_some, Fin.succAbove_castSucc_self, Fin.val_succ]

private noncomputable def insertPair (q : MeshPattern) (a b : Fin (q.k + 1))
    (r : Equiv.Perm (Fin 2)) : Equiv.Perm (Fin (q.k + 2)) :=
  (placeTwo a).symm.trans ((Equiv.sumCongr q.p r).trans (placeTwo b))

@[simp] private lemma insertPair_selected (q : MeshPattern) (a b : Fin (q.k + 1))
    (r : Equiv.Perm (Fin 2)) (i : Fin q.k) :
    insertPair q a b r (skipTwo a i) = skipTwo b (q.p i) := by
  change placeTwo b (Equiv.sumCongr q.p r ((placeTwo a).symm (skipTwo a i))) = _
  rw [← placeTwo_inl a i, Equiv.symm_apply_apply]
  exact placeTwo_inl b (q.p i)

@[simp] private lemma insertPair_gap (q : MeshPattern) (a b : Fin (q.k + 1))
    (r : Equiv.Perm (Fin 2)) (t : Fin 2) :
    insertPair q a b r (gapPoint a t) = gapPoint b (r t) := by
  change placeTwo b (Equiv.sumCongr q.p r ((placeTwo a).symm (gapPoint a t))) = _
  rw [← placeTwo_inr a t, Equiv.symm_apply_apply]
  exact placeTwo_inr b (r t)

private lemma not_range_skipTwo {k : ℕ} (a : Fin (k + 1)) (x : Fin (k + 2))
    (hx : x ∉ Set.range (skipTwo a)) : ∃ t : Fin 2, x = gapPoint a t := by
  obtain ⟨i | t, hi⟩ := (placeTwo a).surjective x
  · rw [placeTwo_inl] at hi
    exact False.elim (hx ⟨i, hi⟩)
  · rw [placeTwo_inr] at hi
    exact ⟨t, hi.symm⟩

private lemma count_gap_positions {k : ℕ} (a : Fin (k + 1)) (t : Fin 2) :
    (Finset.univ.filter fun i : Fin k => skipTwo a i < gapPoint a t).card = a.val := by
  simp only [skipTwo_lt_gap]
  rw [Fin.card_filter_val_lt, Nat.min_eq_right]
  have := a.isLt
  omega

private lemma count_gap_values (q : MeshPattern) (a b : Fin (q.k + 1))
    (r : Equiv.Perm (Fin 2)) (t : Fin 2) :
    (Finset.univ.filter fun i : Fin q.k =>
      insertPair q a b r (skipTwo a i) < insertPair q a b r (gapPoint a t)).card = b.val := by
  simp only [insertPair_selected, insertPair_gap, skipTwo_lt_gap]
  have h := Finset.card_bijective q.p q.p.bijective
    (s := Finset.univ.filter fun i : Fin q.k => (q.p i).val < b.val)
    (t := Finset.univ.filter fun i : Fin q.k => i.val < b.val) (by simp)
  rw [h, Fin.card_filter_val_lt, Nat.min_eq_right]
  have := b.isLt
  omega

private lemma occurs_insertPair (q : MeshPattern) (a b : Fin (q.k + 1))
    (hab : (a, b) ∉ q.R) (r : Equiv.Perm (Fin 2)) :
    Occurs q (insertPair q a b r) := by
  refine ⟨skipTwo a, ?_, ?_⟩
  · intro i j
    simp only [insertPair_selected]
    exact (skipTwo b).lt_iff_lt
  · intro x hx c hc hcell
    obtain ⟨t, rfl⟩ := not_range_skipTwo a x hx
    rw [count_gap_positions, count_gap_values] at hcell
    have hc' : c = (a, b) := Prod.ext (Fin.ext hcell.1) (Fin.ext hcell.2)
    exact hab (hc' ▸ hc)

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

private lemma insertPair_swap (q : MeshPattern) (a b : Fin (q.k + 1)) :
    insertPair q a b (Equiv.swap 0 1) =
      insertPair q a b 1 * Equiv.swap (gapPoint a 0) (gapPoint a 1) := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply]
  obtain ⟨i | t, rfl⟩ := (placeTwo a).surjective x
  · rw [placeTwo_inl,
      Equiv.swap_apply_of_ne_of_ne (skipTwo_ne_gap a i 0) (skipTwo_ne_gap a i 1)]
    simp
  · rw [placeTwo_inr]
    fin_cases t <;> simp

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

private lemma insertPair_sign_flip (q : MeshPattern) (a b : Fin (q.k + 1)) :
    Equiv.Perm.sign (insertPair q a b (Equiv.swap 0 1)) =
      - Equiv.Perm.sign (insertPair q a b 1) := by
  have hne : gapPoint a 0 ≠ gapPoint a 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [gapPoint] at hv
  rw [insertPair_swap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
  simp

private lemma exists_even_extension (q : MeshPattern) (hR : q.R ≠ Set.univ) :
    ∃ σ : Equiv.Perm (Fin (q.k + 2)), Occurs q σ ∧ Equiv.Perm.sign σ = 1 := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := (Set.ne_univ_iff_exists_notMem q.R).mp hR
  rcases Int.units_eq_one_or (Equiv.Perm.sign (insertPair q a b 1)) with hu | hu
  · exact ⟨_, occurs_insertPair q a b hab 1, hu⟩
  · refine ⟨_, occurs_insertPair q a b hab (Equiv.swap 0 1), ?_⟩
    rw [insertPair_sign_flip, hu, neg_neg]

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

private lemma occurs_self (q : MeshPattern) : Occurs q q.p := by
  refine ⟨OrderEmbedding.ofStrictMono id strictMono_id, fun _ _ => Iff.rfl, ?_⟩
  intro x hx
  exact False.elim (hx ⟨x, rfl⟩)

private lemma full_occurs_iff (q : MeshPattern) (hR : q.R = Set.univ)
    {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Occurs q σ ↔ (⟨q.k, q.p⟩ : Σ m : ℕ, Equiv.Perm (Fin m)) = ⟨n, σ⟩ := by
  constructor
  · rintro ⟨e, hpat, hshade⟩
    have hs : Function.Surjective e := by
      intro x
      by_contra hx
      have hp : (Finset.univ.filter fun i : Fin q.k => e i < x).card ≤ q.k := by
        exact card_finset_fin_le _
      have hv : (Finset.univ.filter fun i : Fin q.k => σ (e i) < σ x).card ≤ q.k := by
        exact card_finset_fin_le _
      let c : Fin (q.k + 1) × Fin (q.k + 1) :=
        (⟨_, Nat.lt_succ_of_le hp⟩, ⟨_, Nat.lt_succ_of_le hv⟩)
      exact hshade x hx c (by rw [hR]; trivial) ⟨rfl, rfl⟩
    have hkn : q.k = n := by
      have h := Fintype.card_congr (Equiv.ofBijective e ⟨e.injective, hs⟩)
      simpa using h
    cases q with
    | mk k p R =>
      dsimp only at *
      subst n
      let E : Fin k ≃o Fin k :=
        { toEquiv := Equiv.ofBijective e ⟨e.injective, hs⟩
          map_rel_iff' := e.map_rel_iff }
      have he (i : Fin k) : e i = i := Fin.ext (Fin.coe_orderIso_apply E i)
      simp only [he] at hpat
      let V : Fin k ≃o Fin k :=
        { toEquiv := p.symm.trans σ
          map_rel_iff' := by
            intro i j
            change σ (p.symm i) ≤ σ (p.symm j) ↔ i ≤ j
            have hh : σ (p.symm j) < σ (p.symm i) ↔ j < i := by
              simpa using hpat (p.symm j) (p.symm i)
            simpa only [not_lt] using not_congr hh }
      have hv (i : Fin k) : V i = i := Fin.ext (Fin.coe_orderIso_apply V i)
      have hsp : σ = p := by
        apply Equiv.ext
        intro i
        simpa [V] using hv (p i)
      subst σ
      rfl
  · intro h
    cases q with
    | mk k p R =>
      dsimp only at *
      cases h
      exact occurs_self _

private lemma mesh_ext (q r : MeshPattern)
    (h : (⟨q.k, q.p⟩ : Σ m : ℕ, Equiv.Perm (Fin m)) = ⟨r.k, r.p⟩)
    (hq : q.R = Set.univ) (hr : r.R = Set.univ) : q = r := by
  cases q with
  | mk k p R =>
    cases r with
    | mk n s S =>
      dsimp only at *
      cases h
      subst R
      subst S
      rfl

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

namespace D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis

theorem result : D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis.claim := by
  classical
  intro P hP
  have hfull : ∀ q ∈ P, q.R = Set.univ := by
    intro q hq
    by_contra hR
    obtain ⟨σ, hoc, hev⟩ := exists_even_extension q hR
    have ha : (⟨q.k + 2, σ⟩ : Σ n : ℕ, Equiv.Perm (Fin n)) ∈ Av P := by
      rw [hP.1]
      exact hev
    exact ha q hq hoc
  apply Set.ext
  intro q
  constructor
  · intro hq
    refine ⟨hfull q hq, ?_⟩
    intro hev
    have ha : (⟨q.k, q.p⟩ : Σ n : ℕ, Equiv.Perm (Fin n)) ∈ Av P := by
      rw [hP.1]
      exact hev
    exact ha q hq (occurs_self q)
  · rintro ⟨hR, hodd⟩
    by_contra hq
    have ha : (⟨q.k, q.p⟩ : Σ n : ℕ, Equiv.Perm (Fin n)) ∈ Av P := by
      intro r hr hoc
      have heq := (full_occurs_iff r (hfull r hr) q.p).mp hoc
      have hrq : r = q := mesh_ext r q heq (hfull r hr) hR
      exact hq (hrq ▸ hr)
    rw [hP.1] at ha
    exact hodd ha

end D5.S3.Combinatorics.MeshPattern.UlfarssonAlternatingMeshBasis
