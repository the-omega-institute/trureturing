/- GID: D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImageClaim; result=D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.witness_dealer_image_refutation; claim=D5/S3/Quantum/Information/GangulyCircuitAccess/Combinatorial.dealerImageClaim
   digest: A seven-vertex circuit-access witness has a proper dealer image. -/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import OmegaBuild.Commands

/-! The binary circuit and dealer-image certificates for Ganguly, arXiv:2611.27300v2, §VI Problem 2. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GangulyCircuitAccess

open scoped Matrix

abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The coefficients of a binary relation in the columns of [I | M]
are (Mx, x), with false standing for the unstarred column. -/
def relationSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : Bits n) : Finset (Fin n × Bool) :=
  Finset.univ.filter fun p => (if p.2 then x p.1 else (M *ᵥ x) p.1) ≠ 0

def admissible {n : ℕ} (C : Finset (Fin n × Bool)) : Prop :=
  ∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)

def isCircuit {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Bits n) : Prop :=
  let C := relationSupport M x
  C.Nonempty ∧ admissible C ∧
    ∀ y : Bits n, (relationSupport M y).Nonempty → ¬ relationSupport M y ⊂ C

instance {n : ℕ} (C : Finset (Fin n × Bool)) : Decidable (admissible C) :=
  inferInstanceAs (Decidable (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)))

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Bits n) :
    Decidable (isCircuit M x) := by
  unfold isCircuit
  infer_instance

def meetsDealer {n : ℕ} (d : Fin n) (C : Finset (Fin n × Bool)) : Prop :=
  (d, false) ∈ C ∨ (d, true) ∈ C

instance {n : ℕ} (d : Fin n) (C : Finset (Fin n × Bool)) :
    Decidable (meetsDealer d C) := by
  unfold meetsDealer
  infer_instance

def playerSupport {n : ℕ} (d : Fin n) (C : Finset (Fin n × Bool)) : Finset (Fin n) :=
  (C.image Prod.fst).erase d

def dealerCircuit {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : Fin n) (x : Bits n) : Prop :=
  isCircuit M x ∧ meetsDealer d (relationSupport M x)

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (d : Fin n) (x : Bits n) :
    Decidable (dealerCircuit M d x) := by
  unfold dealerCircuit
  infer_instance

def circuitAuthorized {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : Fin n) (A : Finset (Fin n)) : Prop :=
  d ∉ A ∧ ∃ x : Bits n, dealerCircuit M d x ∧ playerSupport d (relationSupport M x) ⊆ A

def quantumAccess {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (d : Fin n) : Prop :=
  (∃ A, circuitAuthorized M d A) ∧
    ∀ A B, circuitAuthorized M d A → circuitAuthorized M d B → (A ∩ B).Nonempty

/-- Supersets on the player set preserve membership. -/
theorem circuitAuthorized_mono {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    {d : Fin n} {A B : Finset (Fin n)} (hA : circuitAuthorized M d A)
    (hAB : A ⊆ B) (hB : d ∉ B) : circuitAuthorized M d B := by
  obtain ⟨_, x, hx, hsub⟩ := hA
  exact ⟨hB, x, hx, hsub.trans hAB⟩

/-- Checking the circuit generators suffices for the full access antecedent. -/
theorem quantumAccess_of_generators {n : ℕ} {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    {d : Fin n} (hne : ∃ x, dealerCircuit M d x)
    (hinter : ∀ x y, dealerCircuit M d x → dealerCircuit M d y →
      (playerSupport d (relationSupport M x) ∩ playerSupport d (relationSupport M y)).Nonempty) :
    quantumAccess M d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨_, Finset.notMem_erase _ _, x, hx, Finset.Subset.refl _⟩
  · intro A B hA hB
    obtain ⟨_, x, hx, hxA⟩ := hA
    obtain ⟨_, y, hy, hyB⟩ := hB
    obtain ⟨i, hi⟩ := hinter x y hx hy
    obtain ⟨hiX, hiY⟩ := Finset.mem_inter.mp hi
    exact ⟨i, Finset.mem_inter.mpr ⟨hxA hiX, hyB hiY⟩⟩

def supportedAt {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : Fin n) (A : Finset (Fin n)) (x : Bits n) : Prop :=
  ∀ i : Fin n, i ∉ insert d A → x i = 0 ∧ (M *ᵥ x) i = 0

instance {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : Fin n) (A : Finset (Fin n)) (x : Bits n) :
    Decidable (supportedAt M d A x) := by
  unfold supportedAt
  infer_instance

/-- Local dealer labels from the graph of the adjacency matrix. -/
def dealerImage {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (d : Fin n) (A : Finset (Fin n)) : Set (ZMod 2 × ZMod 2) :=
  {p | ∃ x : Bits n, supportedAt M d A x ∧ p = (x d, (M *ᵥ x) d)}

def witnessEdges : Finset (Fin 7 × Fin 7) :=
  {(0, 1), (0, 2), (0, 4), (0, 6), (1, 2), (1, 3),
    (1, 6), (2, 3), (2, 5), (4, 5), (4, 6), (5, 6)}

def witnessGraph : SimpleGraph (Fin 7) where
  Adj i j := (i, j) ∈ witnessEdges ∨ (j, i) ∈ witnessEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := by
    exact ⟨(show ∀ i : Fin 7, ¬ ((i, i) ∈ witnessEdges ∨ (i, i) ∈ witnessEdges) from by decide)⟩

instance : DecidableRel witnessGraph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i, j) ∈ witnessEdges ∨ (j, i) ∈ witnessEdges))

abbrev witnessDealer : Fin 7 := 4
def witnessPlayers : Finset (Fin 7) := {2, 5, 6}
abbrev witnessMatrix := witnessGraph.adjMatrix (ZMod 2)

def witnessRelation : Bits 7 := fun i => if i = 5 then 1 else 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Decide checks minimality against all 128 relation vectors.
theorem witness_circuit : dealerCircuit witnessMatrix witnessDealer witnessRelation := by
  decide +kernel

theorem witness_authorized : circuitAuthorized witnessMatrix witnessDealer witnessPlayers := by
  refine ⟨by decide, witnessRelation, witness_circuit, ?_⟩
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- Decide checks each local label against all 128 relation vectors.
theorem witness_dealer_image :
    dealerImage witnessMatrix witnessDealer witnessPlayers = {(0, 0), (0, 1)} := by
  ext p
  have h : ∀ q : ZMod 2 × ZMod 2,
      (∃ x : Bits 7, supportedAt witnessMatrix witnessDealer witnessPlayers x ∧
        q = (x witnessDealer, (witnessMatrix *ᵥ x) witnessDealer)) ↔
      (q = (0, 0) ∨ q = (0, 1)) := by decide +kernel
  exact h p

private def witnessMinima : Finset (Finset (Fin 7)) :=
  {{0, 2, 6}, {0, 3, 6}, {0, 5, 6}, {2, 3, 6}, {2, 5, 6}, {3, 5, 6},
    {0, 1, 2, 3}, {0, 1, 2, 5}, {0, 1, 3, 5}, {1, 2, 3, 5}}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
-- The reflection certificate checks all 128 possible relation vectors.
private theorem witness_generators_cover :
    ∀ x : Bits 7, admissible (relationSupport witnessMatrix x) →
      meetsDealer witnessDealer (relationSupport witnessMatrix x) →
      ∃ S ∈ witnessMinima, S ⊆ playerSupport witnessDealer (relationSupport witnessMatrix x) := by
  decide +kernel

theorem witness_quantum_access : quantumAccess witnessMatrix witnessDealer := by
  refine quantumAccess_of_generators ⟨witnessRelation, witness_circuit⟩ ?_
  have hPair : ∀ S ∈ witnessMinima, ∀ T ∈ witnessMinima, (S ∩ T).Nonempty := by
    decide +kernel
  intro x y hx hy
  obtain ⟨S, hS, hSX⟩ := witness_generators_cover x hx.1.2.1 hx.2
  obtain ⟨T, hT, hTY⟩ := witness_generators_cover y hy.1.2.1 hy.2
  obtain ⟨i, hi⟩ := hPair S hS T hT
  obtain ⟨hiS, hiT⟩ := Finset.mem_inter.mp hi
  exact ⟨i, Finset.mem_inter.mpr ⟨hSX hiS, hTY hiT⟩⟩

/-- The universal inclusion in the full-dealer-image family. -/
def dealerImageClaim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (d : Fin n),
    quantumAccess (G.adjMatrix (ZMod 2)) d →
    ∀ A, circuitAuthorized (G.adjMatrix (ZMod 2)) d A →
      dealerImage (G.adjMatrix (ZMod 2)) d A = Set.univ

theorem witness_dealer_image_refutation : ¬ dealerImageClaim := by
  intro h
  have hFull := h 7 witnessGraph witnessDealer witness_quantum_access
    witnessPlayers witness_authorized
  have hLabel : ((1, 0) : ZMod 2 × ZMod 2) ∈ dealerImage witnessMatrix
      witnessDealer witnessPlayers := by
    rw [hFull]
    exact Set.mem_univ _
  rw [witness_dealer_image] at hLabel
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hLabel
  exact (show ¬ (((1, 0) : ZMod 2 × ZMod 2) = (0, 0) ∨
    ((1, 0) : ZMod 2 × ZMod 2) = (0, 1)) from by decide) hLabel

def discarded {n : ℕ} (d : Fin n) (A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ \ insert d A

abbrev Config {n : ℕ} (A : Finset (Fin n)) := (↥A → Fin 2)

/-- Configurations are ordered discarded players first, retained players second. -/
def fullConfig {n : ℕ} (d : Fin n) (A : Finset (Fin n))
    (t : Config (discarded d A) × Config A) (s : Fin 2) : Fin n → Fin 2 :=
  fun i =>
    if hD : i = d then s
    else if hA : i ∈ A then t.2 ⟨i, hA⟩
    else t.1 ⟨i, by simp [discarded, hD, hA]⟩

open scoped BigOperators

/-- The ordered quadratic graph phase. -/
def graphPhase {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (t : Bits n) : ZMod 2 :=
  ∑ i, ∑ j with i < j, M i j * t i * t j

/-- The integer sign of the ordered quadratic graph phase. -/
def signedGraphEntry {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (t : Bits n) : ℤ :=
  (-1) ^ (graphPhase M t).val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The certificate checks 64 entries, each summing over 8 discarded configurations.
theorem witness_signed_cross_zero :
    ∀ a b : Config witnessPlayers,
      (∑ c : Config (discarded witnessDealer witnessPlayers),
        signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers (c, a) 0) *
        signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers (c, b) 1)) =
        0 := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- There are 64 rows and two dealer slices.
theorem witness_signed_gram :
    ∀ s t : Fin 2,
      (∑ p : Config (discarded witnessDealer witnessPlayers) × Config witnessPlayers,
        signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers p s) *
        signedGraphEntry witnessMatrix (fullConfig witnessDealer witnessPlayers p t)) =
        if s = t then 64 else 0 := by
  decide +kernel

theorem witness_dealer_surjective :
    Function.Surjective (fun x : Bits 7 => (x witnessDealer, (witnessMatrix *ᵥ x) witnessDealer)) :=
  fun label => (show ∀ q : ZMod 2 × ZMod 2, ∃ x : Bits 7,
      (x witnessDealer, (witnessMatrix *ᵥ x) witnessDealer) = q from by decide +kernel) label

#print axioms witness_quantum_access
#print axioms witness_authorized
#print axioms witness_dealer_image
#print axioms witness_signed_gram
#print axioms witness_dealer_surjective
#print axioms witness_dealer_image_refutation
#print axioms witness_signed_cross_zero

end D5.S3.Quantum.Information.GangulyCircuitAccess
