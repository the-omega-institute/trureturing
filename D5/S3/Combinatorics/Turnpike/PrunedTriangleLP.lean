/- GID: D5/S3/Combinatorics/Turnpike/PrunedTriangleLP
   generality: G
   mirror-B: none(waiver:covered-by-containment-rank-bounds-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Containment masks and singleton marginal cuts -/

module

public import D5.S3.Combinatorics.Turnpike.TriangleLP

/-! Omega original.
# Containment masks and singleton marginal cuts

The rank bounds use closed multiplicity blocks, with zero-based Lean indices.
The cuts quantify over all labels, including empty completion sets.
-/
@[expose] public section
namespace Omega.Turnpike
open scoped BigOperators
noncomputable section

def RankAllowed {n d : ℕ} (μ : Fin d → ℕ) (e : Interval n) (q : Fin d) : Prop :=
  (e.1.1.val + 1) * (n - e.1.2.val) ≤ ∑ r ∈ Finset.univ.filter (· ≤ q), μ r ∧
  (∑ r ∈ Finset.univ.filter (· < q), μ r) + 1 ≤
    n.choose 2 - (e.1.2.val - e.1.1.val + 1).choose 2 + 1

noncomputable def rankMask {n d : ℕ} (μ : Fin d → ℕ)
    (e : Interval n) (q : Fin d) : ℝ := by
  classical
  exact if RankAllowed μ e q then 1 else 0

def ProductAllowed {n d : ℕ} (μ : Fin d → ℕ) (τ : Triangle n)
    (r : Fin d × Fin d × Fin d) : Prop :=
  RankAllowed μ (first τ) r.1 ∧ RankAllowed μ (second τ) r.2.1 ∧
    RankAllowed μ (outer τ) r.2.2

def PrunedDomain {n d : ℕ} (μ : Fin d → ℕ) (P : Assignment n d) : Prop :=
  AssignmentDomain μ P ∧ ∀ e q, P e q ≤ rankMask μ e q

def PrunedBlock {n d : ℕ} {y : Fin d → ℝ} {μ : Fin d → ℕ}
    (P : Assignment n d) (τ : Triangle n) (T : Relation y μ → ℝ) : Prop :=
  Block P τ T ∧ ∀ r, T r ≤
    rankMask μ (first τ) r.1.1 * rankMask μ (second τ) r.1.2.1 *
      rankMask μ (outer τ) r.1.2.2

def PrunedProjection {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (H : Triangle n → Prop) : Set (Assignment n d) :=
  {P | PrunedDomain μ P ∧ ∃ T : {τ : Triangle n // H τ} → Relation y μ → ℝ,
    ∀ τ, PrunedBlock P τ.1 (T τ)}

/-- The three unordered position pairs are represented by their missing position. -/
def coordinate {d : ℕ} (u : Fin 3) (r : Fin d × Fin d × Fin d) : Fin d :=
  if u = 0 then r.1 else if u = 1 then r.2.1 else r.2.2

def edge {n : ℕ} (τ : Triangle n) (u : Fin 3) : Interval n :=
  if u = 0 then first τ else if u = 1 then second τ else outer τ

def Completion {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (τ : Triangle n) (u v w : Fin 3) (a b : Fin d) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun c => ∃ r : Relation y μ,
    ProductAllowed μ τ r.1 ∧ coordinate u r.1 = a ∧
      coordinate v r.1 = b ∧ coordinate w r.1 = c

def SingletonCuts {n d : ℕ} (y : Fin d → ℝ) (μ : Fin d → ℕ)
    (P : Assignment n d) : Prop :=
  ∀ τ : Triangle n, ∀ u v w : Fin 3, u < v → w ≠ u → w ≠ v →
    ∀ a b : Fin d, P (edge τ u) a + P (edge τ v) b ≤
      1 + ∑ c ∈ Completion y μ τ u v w a b, P (edge τ w) c

/-- Finite weighted atoms eliminate the ambient relation sum before arithmetic. -/
def weightedAtoms {α : Type*} [DecidableEq α] {k : ℕ}
    (a : Fin k → α) (z : Fin k → ℝ) (r : α) : ℝ :=
  ∑ s, z s * atom (a s) r

theorem weightedAtoms_sum {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (a : Fin k → α) (z : Fin k → ℝ) :
    ∑ r, weightedAtoms a z r = ∑ s, z s := by
  classical
  simp only [weightedAtoms]
  rw [Finset.sum_comm]
  simp [atom, ← Finset.mul_sum]

theorem weightedAtoms_marginal {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] {k : ℕ} (a : Fin k → α) (z : Fin k → ℝ)
    (f : α → β) (q : β) :
    (∑ r, if f r = q then weightedAtoms a z r else 0) =
      ∑ s, if f (a s) = q then z s else 0 := by
  classical
  have hs : ∀ r, (if f r = q then weightedAtoms a z r else 0) =
      ∑ s, if f r = q then z s * atom (a s) r else 0 := by
    intro r
    split_ifs <;> simp_all [weightedAtoms]
  simp_rw [hs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_eq_single (a s)]
  · simp [atom]
  · intro b _ hb
    simp [atom,hb]
  · simp
end
end Omega.Turnpike
