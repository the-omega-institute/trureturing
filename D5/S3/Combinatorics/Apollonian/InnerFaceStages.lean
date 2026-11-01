/- GID: D5/S3/Combinatorics/Apollonian/InnerFaceStages
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/InnerFaceStages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: Inner-face subdivision constructs the deterministic Apollonian stages. -/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Omega
import Mathlib.Tactic.NormNum

/-! The ordered inner triangles are precisely the faces that are subdivided.
The outer triangle has vertices 0,1,2; seed vertex 3 is its centre.
Source: Rad Sarar Anando, MathOverflow question 516405, revision 1,
8C9D6CD5-E3A3-4B25-BDB6-FF5A9A3D3A2B, CC BY-SA 4.0.
https://mathoverflow.net/questions/516405
-/

namespace D5.S3.Combinatorics.Apollonian.InnerFaceStages

open scoped BigOperators

/-- An inner face at the indicated stage. Each child is indexed by its omitted corner. -/
def Face : ℕ → Type
  | 0 => Fin 3
  | n + 1 => Face n × Fin 3

/-- Old vertices persist, and a distinct new vertex is inserted in each inner face. -/
def Vertex : ℕ → Type
  | 0 => Fin 4
  | n + 1 => Vertex n ⊕ Face n

instance faceFintype : (n : ℕ) → Fintype (Face n)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | n + 1 => @instFintypeProd _ _ (faceFintype n) inferInstance

instance faceDecidableEq : (n : ℕ) → DecidableEq (Face n)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | n + 1 => inferInstanceAs (DecidableEq (Face n × Fin 3))

instance vertexFintype : (n : ℕ) → Fintype (Vertex n)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | n + 1 => @Sum.instFintype _ _ (vertexFintype n) (faceFintype n)

instance vertexDecidableEq : (n : ℕ) → DecidableEq (Vertex n)
  | 0 => inferInstanceAs (DecidableEq (Fin 4))
  | n + 1 => inferInstanceAs (DecidableEq (Vertex n ⊕ Face n))

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
    · exact ih f (Sum.inl.inj (by simpa [corner, hj, hk] using h))

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
  symm := by
    induction n with
    | zero => exact Ne.symm
    | succ n ih => intro u v; cases u <;> cases v <;> simp_all [adjacent]
  loopless := by
    induction n with
    | zero => intro u; exact not_not_intro rfl
    | succ n ih => intro u; cases u <;> simp_all [adjacent]

instance graphDecidable (n : ℕ) : DecidableRel (graph n).Adj := adjacentDecidable n

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
    · exact ⟨j, hj, Sum.inl.inj (by simpa [hj] using h)⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, by simp [hj, h]⟩

private theorem incident_child_new (n : ℕ) (f g : Face n) (i : Fin 3) :
    Incident (n + 1) (f, i) (Sum.inr g) ↔ f = g := by
  constructor
  · rintro ⟨j, h⟩
    by_cases hj : j = i
    · simpa [corner, hj] using h
    · simp [corner, hj] at h
  · intro h; subst g; exact ⟨i, by simp [corner]⟩

private theorem old_incident_children (n : ℕ) (f : Face n) (v : Vertex n) :
    (∑ i : Fin 3, if Incident (n + 1) (f, i) (Sum.inl v) then 1 else 0) =
      if Incident n f v then 2 else 0 := by
  classical
  by_cases h : Incident n f v
  · rcases h with ⟨j, rfl⟩
    have hi := corner_injective n f
    simp only [incident_child_old, hi.eq_iff]
    fin_cases j <;> decide
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
  simp [faceCount, Face, Fintype.sum_prod_type, incident_child_new]

/-- The ordinary adjacency row gains exactly one neighbour per incident inner face. -/
theorem degreeCount_old (n : ℕ) (v : Vertex n) :
    degreeCount (n + 1) (Sum.inl v) = degreeCount n v + faceCount n v := by
  simp [degreeCount, Vertex, Fintype.sum_sum_type, adjacent, faceCount]

/-- New vertices have exactly the three distinct corners of their parent face as neighbours. -/
theorem degreeCount_new (n : ℕ) (f : Face n) :
    degreeCount (n + 1) (Sum.inr f) = 3 := by
  classical
  simp only [degreeCount, Vertex, Fintype.sum_sum_type, adjacent, ite_false, Finset.sum_const_zero,
    add_zero]
  have he : (Finset.univ.filter fun v => Incident n f v) =
      Finset.univ.image (corner n f) := by ext v; simp [Incident]
  rw [← Finset.card_filter, he, Finset.card_image_of_injective _ (corner_injective n f)]
  simp

end D5.S3.Combinatorics.Apollonian.InnerFaceStages
