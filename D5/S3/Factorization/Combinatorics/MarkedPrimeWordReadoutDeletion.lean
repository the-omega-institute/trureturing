/- GID: D5/S3/Factorization/Combinatorics/MarkedPrimeWordReadoutDeletion
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/MarkedPrimeWordReadoutDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked prime words read out strict divisor chains with uniform internal-vertex deletion. -/

import D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber
import D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
import D5.S3.Entropy.Forgetting.PushforwardComposition
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace D5.S3.Factorization.Combinatorics.MarkedPrimeWordReadoutDeletion
open D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber
open D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.Forgetting.PushforwardComposition

/-- Prime words form a finite type by permutation of the prime factor list. -/
noncomputable instance wordFintype (n : ℕ) : Fintype (PrimeWord n) := by
  classical
  let f : PrimeWord n → ↥(n.primeFactorsList.permutations.toFinset) :=
    fun w => ⟨w.val, List.mem_toFinset.mpr (List.mem_permutations.mpr
      (Nat.primeFactorsList_unique w.property.2 w.property.1))⟩
  apply Fintype.ofInjective f
  intro x y h
  exact Subtype.ext (congrArg (fun z : ↥(n.primeFactorsList.permutations.toFinset) => z.val) h)

/-- The total prime multiplicity of the endpoint. -/
def omegaCount (n : ℕ) : ℕ := n.factorization.sum (fun _ a => a)
/-- Internal word positions, with one added to each index to obtain a prefix length. -/
abbrev Positions (n : ℕ) := Fin (omegaCount n - 1)
/-- A set of exactly k minus one internal word positions. -/
def Marks (n k : ℕ) := {I : Finset (Positions n) // I.card = k-1}
/-- A prime word together with its selected internal positions. -/
def U (n k : ℕ) := PrimeWord n × Marks n k
/-- Mark selections and marked prime words have finite carriers. -/
instance (n k : ℕ) : Fintype (Marks n k) := inferInstanceAs (Fintype {_I : Finset (Positions n) // _})
/-- Mark selections and marked prime words have finite carriers. -/
instance (n k : ℕ) : Fintype (U n k) := inferInstanceAs (Fintype (PrimeWord n × Marks n k))
/-- The endpoints and the actual prefix products at the increasingly sorted selected positions. -/
def qList {n : ℕ} (w : PrimeWord n) (I : Finset (Positions n)) : List ℕ :=
  [1] ++ ((I.sort (· ≤ ·)).map fun j => (w.val.take (j.val+1)).prod) ++ [n]
/-- The list readout of a marked prime word. -/
def Q (n k : ℕ) (z : U n k) : List ℕ := qList z.1 z.2.val

/-- The word mass divided equally among all subsets of the prescribed size. -/
noncomputable def μ (n k : ℕ) (w : PrimeWord n → ℝ) (z : U n k) : ℝ :=
  w z.1 / ((omegaCount n-1).choose (k-1) : ℝ)
/-- The mass on readout lists obtained by summing the marked word masses over each fibre. -/
noncomputable def p (n k : ℕ) (w : PrimeWord n → ℝ) : List ℕ → ℝ := pushforward (Q n k) (μ n k w)
/-- The readout mass after weighting each word by its Boltzmann factor. -/
noncomputable def Z (n k : ℕ) (w J : PrimeWord n → ℝ) (β : ℝ) : List ℕ → ℝ :=
  p n k (fun γ => w γ * Real.exp (-β * J γ))
/-- The logarithmic effective cost associated with the Boltzmann readout mass. -/
noncomputable def F (n k : ℕ) (w J : PrimeWord n → ℝ) (β : ℝ) (d : List ℕ) : ℝ :=
  -β⁻¹ * Real.log (Z n k w J β d)
/-- The ordered list of vertices of a strict divisor chain. -/
def chainList {n k : ℕ} (d : Chain n k) : List ℕ := List.ofFn (fun i => (d.val i).val)
/-- One internal vertex of the longer strict chain is omitted. -/
def Deletes {n k : ℕ} (d' : Chain n (k+1)) (d : Chain n k) : Prop :=
  ∃ j : Fin k, ∀ i : Fin (k+1),
    (d.val i).val = (d'.val ((j.succ.castSucc).succAbove i)).val
/-- The kernel assigns one over k to each internal-vertex deletion and zero otherwise. -/
noncomputable def deletionKernel (n k : ℕ) (d' : Chain n (k+1)) (d : Chain n k) : ℝ := by
  classical
  exact if Deletes d' d then 1/(k : ℝ) else 0


/-- A prime word with strictly increasing prefix lengths including both endpoints. -/
def RawMarked (n k : ℕ) :=
  {z : PrimeWord n × (Fin (k+1) → ℕ) //
    z.2 0 = 0 ∧ z.2 (Fin.last k) = z.1.val.length ∧ StrictMono z.2}
/-- Actual prefix products along an increasing list of marks. -/
def QNat {n k : ℕ} (z : RawMarked n k) : Fin (k+1) → ℕ :=
  fun i => (z.val.1.val.take (z.val.2 i)).prod
/-- The fibre of the prefix-product readout over a prescribed vertex sequence. -/
def QFiber (n k : ℕ) (d : Fin (k+1) → ℕ) := {z : RawMarked n k // QNat z = d}

/-- The prefix-product equality fibre is the corresponding snapshot fibre. -/
def fibreEquiv (n k : ℕ) (d : Fin (k+1) → ℕ) :
    QFiber n k d ≃ SnapshotFiber n k d where
  toFun z := ⟨z.val.val, z.val.property.1, z.val.property.2.1,
    z.val.property.2.2, fun i => congrFun z.property i⟩
  invFun z := ⟨⟨z.val, z.property.1, z.property.2.1, z.property.2.2.1⟩,
    funext z.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- Increasing marked prefix products define a bounded strict divisor chain. -/
def qChain {n k : ℕ} (z : RawMarked n k) : Chain n k := by
  let w := z.val.1.val
  have hp : ∀ p ∈ w, Nat.Prime p := z.val.1.property.1
  have hpos (i : ℕ) : 0 < (w.take i).prod :=
    List.prod_pos (fun p h => (hp p (List.mem_of_mem_take h)).pos)
  have hmono : StrictMono (fun i : Fin (w.length+1) => (w.take i.val).prod) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    change (w.take i.val).prod < (w.take (i.val+1)).prod
    rw [List.prod_take_succ w i.val i.isLt]
    exact lt_mul_of_one_lt_right (hpos _) (hp _ (List.getElem_mem i.isLt)).one_lt
  have hmarkbound (i : Fin (k+1)) : z.val.2 i ≤ w.length := by
    rw [← z.property.2.1]
    exact z.property.2.2.monotone (Fin.le_last i)
  have hbound (i : Fin (k+1)) : QNat z i ≤ n := by
    have h := hmono.monotone (show (⟨z.val.2 i, Nat.lt_succ_of_le (hmarkbound i)⟩ : Fin (w.length+1)) ≤ Fin.last w.length by exact hmarkbound i)
    simpa only [Fin.val_last, List.take_length, w, z.val.1.property.2, QNat] using h
  refine ⟨(fun i => ⟨QNat z i, Nat.lt_succ_of_le (hbound i)⟩), ?_, ?_, ?_⟩
  · simp [QNat, z.property.1]
  · simpa only [QNat, z.property.2.1, List.take_length] using z.val.1.property.2
  · intro i
    have hle : z.val.2 i.castSucc ≤ z.val.2 i.succ :=
      z.property.2.2.monotone (Fin.castSucc_le_succ i)
    constructor
    · have he := List.prod_take_mul_prod_drop (w.take (z.val.2 i.succ)) (z.val.2 i.castSucc)
      rw [List.take_take, Nat.min_eq_left hle] at he
      exact ⟨_, he.symm⟩
    · exact hmono (show (⟨z.val.2 i.castSucc, Nat.lt_succ_of_le (hmarkbound _)⟩ : Fin (w.length+1)) <
        ⟨z.val.2 i.succ, Nat.lt_succ_of_le (hmarkbound _)⟩ from z.property.2.2 (Fin.castSucc_lt_succ (i := i)))

/-- The actual strict-chain readout fibre is the corresponding snapshot fibre. -/
def actualChainFibreEquiv (n k : ℕ) (d : Chain n k) :
    {z : RawMarked n k // qChain z = d} ≃ SnapshotFiber n k (fun i => (d.val i).val) := by
  have heq (z : RawMarked n k) : qChain z = d ↔ QNat z = (fun i => (d.val i).val) := by
    constructor
    · intro h
      subst d
      rfl
    · intro h
      apply Subtype.ext
      funext i
      apply Fin.ext
      exact congrFun h i
  exact (Equiv.subtypeEquivRight heq).trans (fibreEquiv n k (fun i => (d.val i).val))


end D5.S3.Factorization.Combinatorics.MarkedPrimeWordReadoutDeletion
