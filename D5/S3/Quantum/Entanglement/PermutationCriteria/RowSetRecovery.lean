/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/RowSetRecovery
   mirror-E: none(waiver:combinatorial reconstruction)
   anchors: []
   utility: none
   digest: Local side labels recover interleaved subsets up to exchange and complement. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria

open _root_.Matrix Finset
open D5.S3.Quantum.Foundation.FiniteTraceDistance

abbrev Index (r d : ℕ) := Fin r → Fin d

abbrev IsDensity := @D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity

/-- The ket position of a tensor factor in the interleaved convention. -/
def ketPos {r : ℕ} (k : Fin r) : Fin (2 * r) := ⟨2 * k.val, by omega⟩

/-- The bra position of a tensor factor in the interleaved convention. -/
def braPos {r : ℕ} (k : Fin r) : Fin (2 * r) := ⟨2 * k.val + 1, by omega⟩

/-- The tensor factor containing a position. -/
def party {r : ℕ} (p : Fin (2 * r)) : Fin r := ⟨p.val / 2, by omega⟩

/-- Interleave row and column coordinates. -/
def merge {r d : ℕ} (a b : Index r d) (p : Fin (2 * r)) : Fin d :=
  if p.val % 2 = 0 then a (party p) else b (party p)

/-- Read an operator at interleaved coordinates. -/
def entry {r d : ℕ} (ρ : Matrix (Index r d) (Index r d) ℂ)
    (i : Fin (2 * r) → Fin d) : ℂ :=
  ρ (fun k => i (ketPos k)) (fun k => i (braPos k))

/-- The index permutation in Clarisse--Wocjan, Section II. -/
def permute {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r)))
    (ρ : Matrix (Index r d) (Index r d) ℂ) : Matrix (Index r d) (Index r d) ℂ :=
  fun a b => entry ρ (fun p => merge a b (σ p))

/-- Equality of the trace norms on every positive trace-one operator. -/
def Dependent (r d : ℕ) (σ μ : Equiv.Perm (Fin (2 * r))) : Prop :=
  ∀ ρ : Matrix (Index r d) (Index r d) ℂ, IsDensity ρ →
    traceNorm (permute σ ρ) = traceNorm (permute μ ρ)

/-- Original index positions which the permutation sends to output row slots. -/
def rowSet {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) : Finset (Fin (2 * r)) :=
  univ.filter (fun p => (σ p).val % 2 = 0)

@[simp] theorem party_ketPos {r : ℕ} (k : Fin r) : party (ketPos k) = k := by
  apply Fin.ext
  simp [party, ketPos]

@[simp] theorem party_braPos {r : ℕ} (k : Fin r) : party (braPos k) = k := by
  apply Fin.ext
  dsimp [party, braPos]
  omega

@[simp] theorem merge_ketPos {r d : ℕ} (a b : Index r d) (k : Fin r) :
    merge a b (ketPos k) = a k := by
  simp [merge, ketPos, party]

@[simp] theorem merge_braPos {r d : ℕ} (a b : Index r d) (k : Fin r) :
    merge a b (braPos k) = b k := by
  have h : (2 * k.val + 1) % 2 ≠ 0 := by omega
  simp [merge, braPos, party, h, Nat.add_div]

theorem ketPos_party {r : ℕ} (p : Fin (2 * r)) (hp : p.val % 2 = 0) :
    ketPos (party p) = p := by
  apply Fin.ext
  dsimp [ketPos, party]
  omega

theorem braPos_party {r : ℕ} (p : Fin (2 * r)) (hp : p.val % 2 ≠ 0) :
    braPos (party p) = p := by
  apply Fin.ext
  dsimp [braPos, party]
  omega

theorem merge_projections {r d : ℕ} (i : Fin (2 * r) → Fin d) :
    merge (fun k => i (ketPos k)) (fun k => i (braPos k)) = i := by
  funext p
  by_cases hp : p.val % 2 = 0
  · simp [merge, hp, ketPos_party p hp]
  · simp [merge, hp, braPos_party p hp]

/-- The simultaneous exchange of the ket and bra positions of every factor. -/
def J (r : ℕ) : Equiv.Perm (Fin (2 * r)) :=
  Function.Involutive.toPerm (fun p => if p.val % 2 = 0 then braPos (party p)
    else ketPos (party p)) (by
      intro p
      dsimp only
      split_ifs <;> apply Fin.ext <;> dsimp [braPos, ketPos, party] at * <;> omega)

@[simp] theorem J_ketPos {r : ℕ} (k : Fin r) : J r (ketPos k) = braPos k := by
  simp [J, ketPos, party]

@[simp] theorem J_braPos {r : ℕ} (k : Fin r) : J r (braPos k) = ketPos k := by
  have h : (2 * k.val + 1) % 2 ≠ 0 := by omega
  simp [J, braPos, party, h, Nat.add_div]

theorem merge_J {r d : ℕ} (a b : Index r d) (p : Fin (2 * r)) :
    merge a b (J r p) = merge b a p := by
  by_cases hp : p.val % 2 = 0
  · rw [← ketPos_party p hp, J_ketPos, merge_braPos, merge_ketPos]
  · rw [← braPos_party p hp, J_braPos, merge_ketPos, merge_braPos]

theorem permute_output_exchange {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r)))
    (ρ : Matrix (Index r d) (Index r d) ℂ) :
    permute (σ.trans (J r)) ρ = (permute σ ρ)ᵀ := by
  ext a b
  simp [permute, Equiv.trans_apply, merge_J, Matrix.transpose_apply]

/-- Interleaving is an equivalence between pairs of tensor indices and flat indices. -/
def mergeEquiv (r d : ℕ) : Index r d × Index r d ≃ (Fin (2 * r) → Fin d) where
  toFun x := merge x.1 x.2
  invFun i := (fun k => i (ketPos k), fun k => i (braPos k))
  left_inv x := by
    apply Prod.ext <;> funext k
    · exact merge_ketPos _ _ _
    · exact merge_braPos _ _ _
  right_inv := merge_projections

/-- Pull back a pair of tensor indices by a permutation of all flat positions. -/
def indexPermutation {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    Equiv.Perm (Index r d × Index r d) :=
  (mergeEquiv r d).trans ((Equiv.arrowCongr σ (Equiv.refl (Fin d))).symm.trans
    (mergeEquiv r d).symm)

theorem permute_apply {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r)))
    (ρ : Matrix (Index r d) (Index r d) ℂ) (a b : Index r d) :
    permute σ ρ a b =
      ρ (indexPermutation σ (a, b)).1 (indexPermutation σ (a, b)).2 := by
  rfl

theorem permute_single {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r)))
    (a b : Index r d) (z : ℂ) :
    permute σ (Matrix.single a b z) =
      Matrix.single ((indexPermutation σ).symm (a, b)).1
        ((indexPermutation σ).symm (a, b)).2 z := by
  ext x y
  simp only [permute_apply, Matrix.single_apply]
  congr 1
  apply propext
  rw [← Prod.mk.injEq, ← Prod.mk.injEq, Prod.mk.eta, Prod.mk.eta]
  exact (indexPermutation σ).symm_apply_eq.symm

end D5.S3.Quantum.Entanglement.PermutationCriteria

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery

open LabelRecovery

/-- The ket and bra side labels of one factor for an interleaved subset. -/
def rowLabels {r : ℕ} (S : Finset (Fin (2 * r))) (k : Fin r) : Bool × Bool :=
  (decide (ketPos k ∈ S), decide (braPos k ∈ S))

private theorem rowLabels_ext {r : ℕ} {S T : Finset (Fin (2 * r))}
    (h : ∀ k, rowLabels T k = rowLabels S k) : T = S := by
  apply Finset.ext
  intro p
  by_cases hp : p.val % 2 = 0
  · have he := ketPos_party p hp
    have hh := congrArg Prod.fst (h (party p))
    change decide (ketPos (party p) ∈ T) = decide (ketPos (party p) ∈ S) at hh
    rw [he] at hh
    exact decide_eq_decide.mp hh
  · have he := braPos_party p hp
    have hh := congrArg Prod.snd (h (party p))
    change decide (braPos (party p) ∈ T) = decide (braPos (party p) ∈ S) at hh
    rw [he] at hh
    exact decide_eq_decide.mp hh

private theorem rowLabels_compl {r : ℕ} (S : Finset (Fin (2 * r))) (k : Fin r) :
    rowLabels Sᶜ k = transform false true (rowLabels S k) := by
  simp [rowLabels, transform]

private theorem rowLabels_map_J {r : ℕ} (S : Finset (Fin (2 * r))) (k : Fin r) :
    rowLabels (S.map (J r).toEmbedding) k = transform true false (rowLabels S k) := by
  have hJ : (J r).symm = J r := rfl
  simp [rowLabels, Finset.mem_map_equiv, hJ, transform]

private theorem rowLabels_map_J_compl {r : ℕ} (S : Finset (Fin (2 * r))) (k : Fin r) :
    rowLabels (S.map (J r).toEmbedding)ᶜ k = transform true true (rowLabels S k) := by
  rw [rowLabels_compl, rowLabels_map_J]
  simp [transform]

/-- Same-side membership and all paired-label distances determine the interleaved
subset up to simultaneous ket-bra exchange and complementation. -/
theorem recover_rowSets {r : ℕ} (S T : Finset (Fin (2 * r)))
    (hside : ∀ k, sameSide (rowLabels S k) ↔ sameSide (rowLabels T k))
    (hdist : ∀ i j,
      pairDistance (rowLabels S i) (rowLabels S j) =
        pairDistance (rowLabels T i) (rowLabels T j)) :
    T = S ∨ T = Sᶜ ∨ T = S.map (J r).toEmbedding ∨
      T = (S.map (J r).toEmbedding)ᶜ := by
  obtain ⟨swap, complement, h⟩ := recover_labels (rowLabels S) (rowLabels T) hside hdist
  cases swap <;> cases complement
  · left
    apply rowLabels_ext
    intro k
    simpa [transform] using h k
  · right; left
    apply rowLabels_ext
    intro k
    rw [rowLabels_compl]
    exact h k
  · right; right; left
    apply rowLabels_ext
    intro k
    rw [rowLabels_map_J]
    exact h k
  · right; right; right
    apply rowLabels_ext
    intro k
    rw [rowLabels_map_J_compl]
    exact h k

#print axioms recover_rowSets

end D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
