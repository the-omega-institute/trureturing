/- GID: D5/S3/Combinatorics/Apollonian/InnerFaceStages
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/InnerFaceStages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: Inner-face subdivision constructs the deterministic Apollonian stages. -/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The ordered inner triangles are precisely the faces that are subdivided.
The outer triangle has vertices 0,1,2; seed vertex 3 is its centre.
Source: Rad Sarar Anando, MathOverflow question 516405, revision 1,
8C9D6CD5-E3A3-4B25-BDB6-FF5A9A3D3A2B, CC BY-SA 4.0.
https://mathoverflow.net/questions/516405
-/

@[expose] public section

namespace D5.S3.Combinatorics.Apollonian.InnerFaceStages

open scoped BigOperators

/-- An inner face at the indicated stage. Each child is indexed by its omitted corner. -/
abbrev Face : ℕ → Type
  | 0 => Fin 3
  | n + 1 => Face n × Fin 3

/-- Old vertices persist, and a distinct new vertex is inserted in each inner face. -/
abbrev Vertex : ℕ → Type
  | 0 => Fin 4
  | n + 1 => Vertex n ⊕ Face n

instance faceFintype : (n : ℕ) → Fintype (Face n)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | n + 1 => @instFintypeProd _ _ (faceFintype n) inferInstance

instance faceDecidableEq : (n : ℕ) → DecidableEq (Face n)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | n + 1 => by
    letI := faceDecidableEq n
    exact inferInstanceAs (DecidableEq (Face n × Fin 3))

instance vertexFintype : (n : ℕ) → Fintype (Vertex n)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | n + 1 => by
    letI := vertexFintype n
    exact inferInstanceAs (Fintype (Vertex n ⊕ Face n))

instance vertexDecidableEq : (n : ℕ) → DecidableEq (Vertex n)
  | 0 => inferInstanceAs (DecidableEq (Fin 4))
  | n + 1 => by
    letI := vertexDecidableEq n
    exact inferInstanceAs (DecidableEq (Vertex n ⊕ Face n))

/-- The three corners of every inner face. A child replaces its omitted corner by its centre. -/
def corner : (n : ℕ) → Face n → Fin 3 → Vertex n
  | 0, f, i => if i = 0 then 3 else if i = 1 then f.castSucc else (f + 1).castSucc
  | n + 1, (f, i), j => if j = i then Sum.inr f else Sum.inl (corner n f j)

private theorem corner_injective (n : ℕ) (f : Face n) : Function.Injective (corner n f) := by
  induction n with
  | zero => revert f; decide
  | succ n ih =>
    rcases f with ⟨f, i⟩
    intro j k h
    by_cases hj : j = i <;> by_cases hk : k = i
    · exact hj.trans hk.symm
    · simp [corner, hj, hk] at h
    · simp [corner, hj, hk] at h
    · exact ih f (by simpa [corner, hj, hk] using h)

/-- Membership in the actual corner triple. -/
def Incident (n : ℕ) (f : Face n) (v : Vertex n) : Prop := ∃ i, corner n f i = v

instance incidentDecidable (n : ℕ) (f : Face n) (v : Vertex n) :
    Decidable (Incident n f v) := inferInstanceAs (Decidable (∃ i, corner n f i = v))

/-- Exact unweighted adjacency; no new edges join two old vertices or two new vertices. -/
def adjacent : (n : ℕ) → Vertex n → Vertex n → Prop
  | 0, u, v => u ≠ v
  | n + 1, Sum.inl u, Sum.inl v => adjacent n u v
  | n + 1, Sum.inl u, Sum.inr f => Incident n f u
  | n + 1, Sum.inr f, Sum.inl v => Incident n f v
  | _ + 1, Sum.inr _, Sum.inr _ => False

instance adjacentDecidable : (n : ℕ) → DecidableRel (adjacent n)
  | 0 => inferInstanceAs (DecidableRel fun u v : Fin 4 => u ≠ v)
  | n + 1 => fun u v => by
    cases u <;> cases v <;> simp only [adjacent]
    · exact adjacentDecidable n _ _
    all_goals infer_instance

/-- The finite simple graph obtained by simultaneous subdivision of inner faces only. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj := adjacent n
  symm := ⟨by
    induction n with
    | zero => exact fun _ _ => Ne.symm
    | succ n ih => intro u v; cases u <;> cases v <;> simp_all [adjacent]⟩
  loopless := ⟨by
    induction n with
    | zero => intro u; exact not_not_intro rfl
    | succ n ih => intro u; cases u <;> simp_all [adjacent]⟩

instance graphDecidable (n : ℕ) : DecidableRel (graph n).Adj := adjacentDecidable n

private theorem face_clique (n : ℕ) (f : Face n) (i j : Fin 3) (hij : i ≠ j) :
    adjacent n (corner n f i) (corner n f j) := by
  induction n with
  | zero => exact fun h => hij (corner_injective 0 f h)
  | succ n ih =>
    rcases f with ⟨f, k⟩
    by_cases hi : i = k <;> by_cases hj : j = k
    · exact (hij (hi.trans hj.symm)).elim
    · simp only [corner, hi, hj, ↓reduceIte, adjacent]
      exact ⟨j, rfl⟩
    · simp only [corner, hi, hj, ↓reduceIte, adjacent]
      exact ⟨i, rfl⟩
    · simpa only [corner, hi, hj, ↓reduceIte, adjacent] using ih f

/-- Number of currently incident inner faces. -/
def faceCount (n : ℕ) (v : Vertex n) : ℕ := ∑ f : Face n, if Incident n f v then 1 else 0

/-- Number of inner faces containing both vertices. -/
def pairFaceCount (n : ℕ) (u v : Vertex n) : ℕ :=
  ∑ f : Face n, if Incident n f u ∧ Incident n f v then 1 else 0

/-- Degree, expressed as an adjacency row sum for later block-matrix counting. -/
def degreeCount (n : ℕ) (v : Vertex n) : ℕ :=
  ∑ u : Vertex n, if adjacent n v u then 1 else 0

private theorem incident_child_old (n : ℕ) (f : Face n) (i : Fin 3) (v : Vertex n) :
    Incident (n + 1) (f, i) (Sum.inl v) ↔ ∃ j, j ≠ i ∧ corner n f j = v := by
  simp only [Incident, corner]
  constructor
  · rintro ⟨j, h⟩
    by_cases hj : j = i
    · simp [hj] at h
    · exact ⟨j, hj, by simpa [hj] using h⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, by simp [hj, h]⟩

private theorem incident_child_new (n : ℕ) (f g : Face n) (i : Fin 3) :
    Incident (n + 1) (f, i) (Sum.inr g) ↔ f = g := by
  constructor
  · rintro ⟨j, h⟩
    by_cases hj : j = i
    · simpa [corner, hj] using h
    · simp [corner, hj] at h
  · intro h; subst g; exact ⟨i, by simp [corner]⟩

/-- Distinct inner-face indices describe distinct triangles, without a duplicate-face quotient. -/
theorem inner_faces_distinct (n : ℕ) (f g : Face n)
    (h : ∀ v, Incident n f v ↔ Incident n g v) : f = g := by
  cases n with
  | zero => revert f g; decide
  | succ n =>
    rcases f with ⟨f, i⟩
    rcases g with ⟨g, j⟩
    have hp : g = f := (incident_child_new n g f j).mp
      ((h (Sum.inr f)).mp ((incident_child_new n f f i).mpr rfl))
    subst g
    have hij : i = j := by
      by_contra hij
      have hr := (incident_child_old n f j (corner n f i)).mpr ⟨i, hij, rfl⟩
      obtain ⟨l, hli, hl⟩ := (incident_child_old n f i (corner n f i)).mp
        ((h (Sum.inl (corner n f i))).mpr hr)
      exact hli (corner_injective n f hl)
    exact Prod.ext rfl hij

private theorem old_incident_children (n : ℕ) (f : Face n) (v : Vertex n) :
    (∑ i : Fin 3, if Incident (n + 1) (f, i) (Sum.inl v) then 1 else 0) =
      if Incident n f v then 2 else 0 := by
  classical
  by_cases h : Incident n f v
  · rcases h with ⟨j, rfl⟩
    have hi := corner_injective n f
    simp_rw [incident_child_old]
    simp only [Incident, hi.eq_iff]
    fin_cases j <;> simp only [Fin.sum_univ_succ] <;> decide
  · have hn : ∀ i, ¬ Incident (n + 1) (f, i) (Sum.inl v) := by
      intro i hi
      obtain ⟨j, _, hj⟩ := (incident_child_old n f i v).mp hi
      exact h ⟨j, hj⟩
    simp [hn, h]

/-- Every old incident inner face gives exactly two incident children. -/
theorem faceCount_old (n : ℕ) (v : Vertex n) :
    faceCount (n + 1) (Sum.inl v) = 2 * faceCount n v := by
  classical
  simp only [faceCount, Face, Fintype.sum_prod_type, old_incident_children]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _; split_ifs <;> simp

/-- A newly inserted vertex belongs to exactly its three child faces. -/
theorem faceCount_new (n : ℕ) (f : Face n) :
    faceCount (n + 1) (Sum.inr f) = 3 := by
  classical
  unfold faceCount
  rw [Fintype.sum_prod_type]
  simp only [incident_child_new]
  simp

/-- The ordinary adjacency row gains exactly one neighbour per incident inner face. -/
theorem degreeCount_old (n : ℕ) (v : Vertex n) :
    degreeCount (n + 1) (Sum.inl v) = degreeCount n v + faceCount n v := by
  unfold degreeCount
  rw [Fintype.sum_sum_type]
  rfl

/-- New vertices have exactly the three distinct corners of their parent face as neighbours. -/
private theorem degreeCount_new (n : ℕ) (f : Face n) :
    degreeCount (n + 1) (Sum.inr f) = 3 := by
  classical
  simp only [degreeCount, Vertex, Fintype.sum_sum_type, adjacent, ite_false, Finset.sum_const_zero,
    add_zero]
  let e : Fin 3 ≃ {v : Vertex n // Incident n f v} :=
    Equiv.ofBijective (fun i => ⟨corner n f i, i, rfl⟩) ⟨
      fun _ _ h => corner_injective n f (congrArg Subtype.val h), by
        rintro ⟨v, i, hi⟩
        exact ⟨i, Subtype.ext hi⟩⟩
  rw [← Finset.card_filter, ← Fintype.card_subtype]
  simpa using (Fintype.card_congr e).symm

private theorem pair_old_children (n : ℕ) (f : Face n) (u v : Vertex n) (huv : u ≠ v) :
    (∑ i : Fin 3, if Incident (n + 1) (f, i) (Sum.inl u) ∧
      Incident (n + 1) (f, i) (Sum.inl v) then 1 else 0) =
        if Incident n f u ∧ Incident n f v then 1 else 0 := by
  classical
  by_cases hu : Incident n f u
  · by_cases hv : Incident n f v
    · rcases hu with ⟨j, rfl⟩
      rcases hv with ⟨k, rfl⟩
      have hjk : j ≠ k := fun h => huv (congrArg (corner n f) h)
      have hi := corner_injective n f
      simp_rw [incident_child_old]
      simp only [Incident, hi.eq_iff, exists_eq_right]
      fin_cases j <;> fin_cases k <;> simp only [Fin.sum_univ_succ] <;> norm_num at *
    · have hn : ∀ i, ¬ Incident (n + 1) (f, i) (Sum.inl v) := by
        intro i h; obtain ⟨j, _, hj⟩ := (incident_child_old n f i v).mp h
        exact hv ⟨j, hj⟩
      simp [hn, hv]
  · have hn : ∀ i, ¬ Incident (n + 1) (f, i) (Sum.inl u) := by
      intro i h; obtain ⟨j, _, hj⟩ := (incident_child_old n f i u).mp h
      exact hu ⟨j, hj⟩
    simp [hn, hu]

private theorem pairFaceCount_old (n : ℕ) (u v : Vertex n) (huv : u ≠ v) :
    pairFaceCount (n + 1) (Sum.inl u) (Sum.inl v) = pairFaceCount n u v := by
  simp only [pairFaceCount, Face, Fintype.sum_prod_type, pair_old_children n _ u v huv]

private theorem pairFaceCount_old_new (n : ℕ) (u : Vertex n) (f : Face n) :
    pairFaceCount (n + 1) (Sum.inl u) (Sum.inr f) = if Incident n f u then 2 else 0 := by
  classical
  unfold pairFaceCount
  rw [Fintype.sum_prod_type]
  have h (g : Face n) :
      (∑ i : Fin 3, if Incident (n + 1) (g, i) (Sum.inl u) ∧
        Incident (n + 1) (g, i) (Sum.inr f) then 1 else 0) =
      if g = f then (if Incident n f u then 2 else 0) else 0 := by
    by_cases hg : g = f
    · subst g; simp only [incident_child_new, ↓reduceIte, and_true]
      exact old_incident_children n f u
    · simp [incident_child_new, hg]
  simp_rw [h]
  simp

private theorem pairFaceCount_symm (n : ℕ) (u v : Vertex n) :
    pairFaceCount n u v = pairFaceCount n v u := by simp [pairFaceCount, and_comm]

private theorem pairFaceCount_zero_of_not_adj (n : ℕ) (u v : Vertex n) (huv : u ≠ v)
    (ha : ¬ adjacent n u v) : pairFaceCount n u v = 0 := by
  apply Finset.sum_eq_zero
  intro f _
  split_ifs with hf
  · obtain ⟨i, hi⟩ := hf.1
    obtain ⟨j, hj⟩ := hf.2
    have hij : i ≠ j := by intro h; exact huv (hi.symm.trans ((congrArg (corner n f) h).trans hj))
    exact (ha (by simpa [hi, hj] using face_clique n f i j hij)).elim
  · rfl

/-- Each pair of distinct vertices belongs to at most two current inner faces. -/
private theorem pairFaceCount_le_two (n : ℕ) (u v : Vertex n) (huv : u ≠ v) :
    pairFaceCount n u v ≤ 2 := by
  induction n with
  | zero => revert u v; decide
  | succ n ih =>
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        rw [pairFaceCount_old n u v (fun h => huv (congrArg Sum.inl h))]
        exact ih u v (fun h => huv (congrArg Sum.inl h))
      | inr f => rw [pairFaceCount_old_new]; split_ifs <;> omega
    | inr f =>
      cases v with
      | inl v => rw [pairFaceCount_symm, pairFaceCount_old_new]; split_ifs <;> omega
      | inr g =>
        have hfg : f ≠ g := fun h => huv (congrArg Sum.inr h)
        have hz : pairFaceCount (n + 1) (Sum.inr f) (Sum.inr g) = 0 := by
          simp only [pairFaceCount, Fintype.sum_prod_type, incident_child_new]
          apply Finset.sum_eq_zero
          intro h _
          simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
          intro i _
          split_ifs with hh
          · exact (hfg (hh.1.symm.trans hh.2)).elim
          · rfl
        omega

/-- Canonical inclusion over an arbitrary number of subdivisions. -/
def embed (n : ℕ) : (t : ℕ) → Vertex n → Vertex (n + t)
  | 0, v => v
  | t + 1, v => Sum.inl (embed n t v)

private theorem embed_injective (n t : ℕ) : Function.Injective (embed n t) := by
  induction t with
  | zero => exact Function.injective_id
  | succ t ih => exact Sum.inl_injective.comp ih

/-- Birth is zero for the four seed vertices and is the exact insertion stage otherwise. -/
def birth : (n : ℕ) → Vertex n → ℕ
  | 0, _ => 0
  | n + 1, Sum.inl v => birth n v
  | n + 1, Sum.inr _ => n + 1

private theorem birth_le (n : ℕ) (v : Vertex n) : birth n v ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => cases v with
    | inl v => exact (ih v).trans (Nat.le_succ n)
    | inr f => exact le_rfl

/-- Adjacency between persistent vertices never changes. -/
theorem adjacent_embed (n t : ℕ) (u v : Vertex n) :
    adjacent (n + t) (embed n t u) (embed n t v) ↔ adjacent n u v := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

private theorem birth_embed (n t : ℕ) (v : Vertex n) :
    birth (n + t) (embed n t v) = birth n v := by
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- Old vertices at a later stage are exactly the image of the canonical inclusion. -/
theorem old_vertices_iff (k t : ℕ) (w : Vertex (k + t)) :
    birth (k + t) w ≤ k ↔ ∃ u : Vertex k, embed k t u = w := by
  constructor
  · induction t with
    | zero => exact fun _ => ⟨w, rfl⟩
    | succ t ih =>
      cases w with
      | inl w =>
        intro hw
        obtain ⟨u, hu⟩ := ih w hw
        exact ⟨u, congrArg Sum.inl hu⟩
      | inr f => intro h; change k + t + 1 ≤ k at h; omega
  · rintro ⟨u, rfl⟩
    rw [birth_embed]
    exact birth_le k u

private theorem degreeCount_eq_faceCount (n : ℕ) (v : Vertex n) (hv : 0 < birth n v) :
    degreeCount n v = faceCount n v := by
  induction n with
  | zero => simp [birth] at hv
  | succ n ih =>
    cases v with
    | inl v =>
      rw [degreeCount_old, faceCount_old, ih v hv]
      omega
    | inr f => rw [degreeCount_new, faceCount_new]

/-- Every nonseed vertex has the exact degree prescribed by its birth stage. -/
theorem degreeCount_inner (n : ℕ) (v : Vertex n) (hv : 0 < birth n v) :
    degreeCount n v = 3 * 2 ^ (n - birth n v) := by
  induction n with
  | zero => simp [birth] at hv
  | succ n ih =>
    cases v with
    | inl v =>
      have hb := birth_le n v
      have he : n + 1 - birth n v = (n - birth n v) + 1 := by omega
      simp only [birth, degreeCount_old, ← degreeCount_eq_faceCount n v hv, ih v hv,
        he, pow_succ]
      ring
    | inr f => simp [degreeCount_new, birth]

/-- The late induced graph has degree at most the largest allowed birth-stage degree. -/
theorem degreeCount_late_le (n k : ℕ) (v : Vertex n) (hv : k < birth n v) :
    degreeCount n v ≤ 3 * 2 ^ (n - k - 1) := by
  rw [degreeCount_inner n v (by omega)]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The seed vertices are retained by the canonical old-vertex inclusions. -/
def seed : (n : ℕ) → Fin 4 → Vertex n
  | 0, v => v
  | n + 1, v => Sum.inl (seed n v)

theorem seed_injective (n : ℕ) : Function.Injective (seed n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact Sum.inl_injective.comp ih

/-- The seed centre has degree 3*2^n and each outer corner degree 2^(n+1)+1. -/
theorem seed_degrees (n : ℕ) (v : Fin 4) :
    degreeCount n (seed n v) = if v = 3 then 3 * 2 ^ n else 2 ^ (n + 1) + 1 := by
  have h (n : ℕ) : faceCount n (seed n v) = 2 ^ n * (if v = 3 then 3 else 2) := by
    induction n with
    | zero => revert v; decide
    | succ n ih =>
      change faceCount (n + 1) (Sum.inl (seed n v)) = _
      rw [faceCount_old, ih, pow_succ]
      ring
  induction n with
  | zero => clear h; revert v; decide
  | succ n ih =>
    change degreeCount (n + 1) (Sum.inl (seed n v)) = _
    rw [degreeCount_old, ih, h]
    split_ifs <;> simp only [pow_succ] <;> ring

/-- The actual ordinary graph degree agrees with its row count. -/
theorem degreeCount_eq_degree (n : ℕ) (v : Vertex n) : degreeCount n v = (graph n).degree v := by
  classical
  rw [degreeCount, ← Finset.card_filter]
  unfold SimpleGraph.degree
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  rfl

/-- Four persistent distinct vertices suffice to index the second ordered eigenvalue. -/
theorem card_vertex_ge_four (n : ℕ) : 4 ≤ Fintype.card (Vertex n) := by
  simpa using Fintype.card_le_of_injective (seed n) (seed_injective n)

/-- Common neighbours counted only after the fixed old stage, in the actual later graph. -/
def lateCommonCount (k t : ℕ) (u v : Vertex k) : ℕ :=
  ∑ w : Vertex (k + t), if k < birth (k + t) w ∧
    adjacent (k + t) (embed k t u) w ∧ adjacent (k + t) (embed k t v) w then 1 else 0

private theorem lateCommonCount_zero (k : ℕ) (u v : Vertex k) : lateCommonCount k 0 u v = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  have h := birth_le k w
  simp only [Nat.add_zero] at *
  simp [show ¬ k < birth k w by omega]

private theorem lateCommonCount_succ (k t : ℕ) (u v : Vertex k) :
    lateCommonCount k (t + 1) u v = lateCommonCount k t u v +
      pairFaceCount (k + t) (embed k t u) (embed k t v) := by
  unfold lateCommonCount pairFaceCount
  rw [Fintype.sum_sum_type]
  simp only [embed, adjacent, birth]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  have hl : k < k.add t + 1 := Nat.lt_succ_of_le (Nat.le_add_right k t)
  simp only [hl, true_and]
  rfl

/-- Distinct old vertices gain at most two common new neighbours at each step. -/
private theorem lateCommonCount_le (k t : ℕ) (u v : Vertex k) (huv : u ≠ v) :
    lateCommonCount k t u v ≤ 2 * t := by
  induction t with
  | zero => simp only [lateCommonCount_zero, Nat.mul_zero, le_refl]
  | succ t ih =>
    rw [lateCommonCount_succ]
    have hp := pairFaceCount_le_two (k + t) (embed k t u) (embed k t v)
      (fun h => huv (embed_injective k t h))
    omega

private theorem degreeCount_split (k t : ℕ) (u : Vertex k) :
    degreeCount (k + t) (embed k t u) = degreeCount k u + lateCommonCount k t u u := by
  induction t with
  | zero => simp only [lateCommonCount_zero, embed, Nat.add_zero]
  | succ t ih =>
    change degreeCount (k + t + 1) (Sum.inl (embed k t u)) = _
    rw [degreeCount_old, ih, lateCommonCount_succ]
    have hd : pairFaceCount (k + t) (embed k t u) (embed k t u) =
        faceCount (k + t) (embed k t u) := by simp only [pairFaceCount, and_self, faceCount]
    rw [hd]
    omega

private theorem lateCommonCount_diag (k t : ℕ) (u : Vertex k) :
    lateCommonCount k t u u = degreeCount (k + t) (embed k t u) - degreeCount k u := by
  have h := degreeCount_split k t u
  omega

/-- A late common neighbour can occur only across an edge already present at the cutoff. -/
private theorem lateCommonCount_zero_of_not_adj (k t : ℕ) (u v : Vertex k) (huv : u ≠ v)
    (ha : ¬ adjacent k u v) : lateCommonCount k t u v = 0 := by
  induction t with
  | zero => exact lateCommonCount_zero k u v
  | succ t ih =>
    have hp := pairFaceCount_zero_of_not_adj (k + t) (embed k t u) (embed k t v)
      (fun h => huv (embed_injective k t h)) (fun h => ha ((adjacent_embed k t u v).mp h))
    rw [lateCommonCount_succ, ih, hp, Nat.add_zero]

private theorem adjacent_equal_birth_zero (n : ℕ) (u v : Vertex n) (ha : adjacent n u v)
    (hb : birth n u = birth n v) : birth n u = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases u with
    | inl u =>
      cases v with
      | inl v => exact ih u v ha hb
      | inr f => have hu := birth_le n u; simp only [birth] at hb ⊢; omega
    | inr f =>
      cases v with
      | inl v => have hv := birth_le n v; simp only [birth] at hb ⊢; omega
      | inr g => exact ha.elim

/-- Orient an edge from its younger endpoint to its strictly older endpoint. -/
def Oriented (n : ℕ) (u v : Vertex n) : Prop := adjacent n u v ∧ birth n v < birth n u

instance orientedDecidable (n : ℕ) : DecidableRel (Oriented n) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Every vertex has at most three outgoing edges in the birth orientation. -/
theorem oriented_outdegree_le_three (n : ℕ) (u : Vertex n) :
    (∑ v : Vertex n, if Oriented n u v then 1 else 0) ≤ 3 := by
  induction n with
  | zero => simp [Oriented, birth]
  | succ n ih =>
    cases u with
    | inl u =>
      rw [Fintype.sum_sum_type]
      have hz : ∀ f : Face n, ¬ Oriented (n + 1) (Sum.inl u) (Sum.inr f) := by
        intro f h; have := birth_le n u; simp only [Oriented, birth] at h; omega
      have hb := birth_le n u
      simp only [Oriented, adjacent, birth, show ¬ n + 1 < birth n u by omega,
        and_false, ite_false, Finset.sum_const_zero, add_zero]
      exact ih u
    | inr f =>
      have he : (∑ v : Vertex (n + 1), if Oriented (n + 1) (Sum.inr f) v then 1 else 0) =
          degreeCount (n + 1) (Sum.inr f) := by
        apply Finset.sum_congr rfl
        intro v _
        cases v with
        | inl v => simp [Oriented, birth, Nat.lt_succ_of_le (birth_le n v)]
        | inr g => simp [Oriented, adjacent, birth]
      rw [he, degreeCount_new]

/-- Every edge with both endpoints born after the cutoff has one birth orientation. -/
theorem late_edge_oriented (n k : ℕ) (u v : Vertex n) (hu : k < birth n u)
    (_hv : k < birth n v) (ha : adjacent n u v) : Oriented n u v ∨ Oriented n v u := by
  have hb : birth n u ≠ birth n v := by
    intro h; have := adjacent_equal_birth_zero n u v ha h; omega
  rcases lt_or_gt_of_ne hb with h | h
  · exact Or.inr ⟨(graph n).adj_symm ha, h⟩
  · exact Or.inl ⟨ha, h⟩

/-- The actual late-vertex orientation has the indegree bound used by the remainder estimate. -/
theorem late_oriented_indegree_le (n k : ℕ) (u : Vertex n) (hu : k < birth n u) :
    (∑ v : Vertex n, if k < birth n v ∧ Oriented n v u then 1 else 0) ≤
      3 * 2 ^ (n - k - 1) := by
  apply le_trans (b := degreeCount n u)
  · apply Finset.sum_le_sum
    intro v _
    by_cases h : k < birth n v ∧ Oriented n v u
    · have ha : adjacent n u v := (graph n).adj_symm h.2.1
      simp only [h, ha, and_self, ↓reduceIte, le_refl]
    · simp only [h, ↓reduceIte]
      exact Nat.zero_le _
  · exact degreeCount_late_le n k u hu

/-- The ordinary, real, zero-one adjacency matrix of the constructed simple graph. -/
def adjacency (n : ℕ) : Matrix (Vertex n) (Vertex n) ℝ := (graph n).adjMatrix ℝ

/-- The actual vertices born after the fixed cutoff. -/
abbrev LateVertex (k t : ℕ) := {w : Vertex (k + t) // k < birth (k + t) w}

/-- The cutoff partition, with actual old vertices and actual later-born vertices. -/
noncomputable def cutoffEquiv (k t : ℕ) : Vertex k ⊕ LateVertex k t ≃ Vertex (k + t) :=
  Equiv.ofBijective (Sum.elim (embed k t) Subtype.val) ⟨by
    intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (embed_injective k t h)
      | inr v =>
        change embed k t u = v.val at h
        have hb := v.property
        rw [← h, birth_embed] at hb
        have hu := birth_le k u
        omega
    | inr u =>
      cases v with
      | inl v =>
        change u.val = embed k t v at h
        have hb := u.property
        rw [h, birth_embed] at hb
        have hv := birth_le k v
        omega
      | inr v => exact congrArg Sum.inr (Subtype.ext h), by
    intro w
    by_cases hb : birth (k + t) w ≤ k
    · obtain ⟨u, hu⟩ := (old_vertices_iff k t w).mp hb
      exact ⟨Sum.inl u, hu⟩
    · exact ⟨Sum.inr ⟨w, Nat.lt_of_not_ge hb⟩, rfl⟩⟩

/-- The old-to-late block of the ordinary adjacency matrix, without weights or normalization. -/
def cutoffBlock (k t : ℕ) : Matrix (Vertex k) (LateVertex k t) ℝ :=
  fun u w => adjacency (k + t) (embed k t u) w.val

/-- The ordinary adjacency induced on vertices born after the cutoff. -/
def lateAdjacency (k t : ℕ) : Matrix (LateVertex k t) (LateVertex k t) ℝ :=
  fun u v => adjacency (k + t) u.val v.val

/-- The exact old/new adjacency decomposition under the actual cutoff bijection. -/
theorem cutoff_adjacency (k t : ℕ) (u v : Vertex k ⊕ LateVertex k t) :
    adjacency (k + t) (cutoffEquiv k t u) (cutoffEquiv k t v) =
      Matrix.fromBlocks (adjacency k) (cutoffBlock k t) (cutoffBlock k t).transpose
        (lateAdjacency k t) u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      change (if adjacent (k + t) (embed k t u) (embed k t v) then (1 : ℝ) else 0) =
        if adjacent k u v then 1 else 0
      simp only [adjacent_embed]
    | inr v => rfl
  | inr u =>
    cases v with
    | inl v =>
      change (graph (k + t)).adjMatrix ℝ u.val (embed k t v) =
        (graph (k + t)).adjMatrix ℝ (embed k t v) u.val
      exact ((graph (k + t)).isSymm_adjMatrix (α := ℝ)).apply _ _
    | inr v => rfl

/-- Each Gram entry counts actual common neighbours born after the cutoff. -/
private theorem cutoff_gram_entry (k t : ℕ) (u v : Vertex k) :
    (cutoffBlock k t * (cutoffBlock k t).transpose) u v = (lateCommonCount k t u v : ℝ) := by
  classical
  change (∑ w : LateVertex k t,
    (if adjacent (k + t) (embed k t u) w.val then (1 : ℝ) else 0) *
    (if adjacent (k + t) (embed k t v) w.val then (1 : ℝ) else 0)) = _
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun w : Vertex (k + t) => k < birth (k + t) w)
    (by intro w; simp) (fun w =>
      (if adjacent (k + t) (embed k t u) w then (1 : ℝ) else 0) *
      (if adjacent (k + t) (embed k t v) w then (1 : ℝ) else 0))]
  rw [Finset.sum_filter]
  simp only [lateCommonCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hb : k < birth (k + t) w <;>
    by_cases hu : adjacent (k + t) (embed k t u) w <;>
    by_cases hv : adjacent (k + t) (embed k t v) w <;> simp [hb, hu, hv]

/-- The Gram diagonal is the difference of the two actual ordinary graph degrees. -/
theorem cutoff_gram_diag (k t : ℕ) (u : Vertex k) :
    (cutoffBlock k t * (cutoffBlock k t).transpose) u u =
      (((graph (k + t)).degree (embed k t u) - (graph k).degree u : ℕ) : ℝ) := by
  rw [cutoff_gram_entry, lateCommonCount_diag, degreeCount_eq_degree, degreeCount_eq_degree]

/-- Uniform linear off-diagonal bound on the actual old-to-late Gram matrix. -/
theorem cutoff_gram_offdiag (k t : ℕ) (u v : Vertex k) (huv : u ≠ v) :
    0 ≤ (cutoffBlock k t * (cutoffBlock k t).transpose) u v ∧
      (cutoffBlock k t * (cutoffBlock k t).transpose) u v ≤ 2 * (t : ℝ) ∧
      (¬ adjacent k u v → (cutoffBlock k t * (cutoffBlock k t).transpose) u v = 0) := by
  rw [cutoff_gram_entry]
  constructor
  · exact Nat.cast_nonneg _
  · constructor
    · exact_mod_cast lateCommonCount_le k t u v huv
    · intro ha
      rw [lateCommonCount_zero_of_not_adj k t u v huv ha, Nat.cast_zero]

/-- The zero-based index one, with its bound supplied by the persistent seed vertices. -/
def secondIndex (n : ℕ) : Fin (Fintype.card (Vertex n)) :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 4) (card_vertex_ge_four n)⟩

/-- The second largest real eigenvalue of ordinary adjacency, counting multiplicity. -/
noncomputable def secondEigenvalue (n : ℕ) : ℝ :=
  ((graph n).isHermitian_adjMatrix ℝ).eigenvalues₀ (secondIndex n)

/-- The original all-natural-stage limit, proved in `SecondEigenvalueLimit.result`. -/
def limitClaim : Prop :=
  Filter.Tendsto (fun n : ℕ => secondEigenvalue n / (2 : ℝ) ^ ((n : ℝ) / 2))
    Filter.atTop (nhds (Real.sqrt 2))

end D5.S3.Combinatorics.Apollonian.InnerFaceStages
