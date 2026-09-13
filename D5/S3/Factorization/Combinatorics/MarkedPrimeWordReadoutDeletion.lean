/- GID: D5/S3/Factorization/Combinatorics/MarkedPrimeWordReadoutDeletion
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/MarkedPrimeWordReadoutDeletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked prime word readouts obey uniform internal-vertex deletion. -/

import D5.S3.Factorization.Combinatorics.MarkedPrimeWordSnapshotFiber
import D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
import D5.S3.Entropy.Forgetting.PushforwardComposition
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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
instance (n k : ℕ) : Fintype (Marks n k) :=
  inferInstanceAs (Fintype {_I : Finset (Positions n) // _})
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
    have h := hmono.monotone (show
      (⟨z.val.2 i, Nat.lt_succ_of_le (hmarkbound i)⟩ : Fin (w.length+1)) ≤
        Fin.last w.length from hmarkbound i)
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
    · exact hmono (show
        (⟨z.val.2 i.castSucc, Nat.lt_succ_of_le (hmarkbound _)⟩ : Fin (w.length+1)) <
          ⟨z.val.2 i.succ, Nat.lt_succ_of_le (hmarkbound _)⟩ from
            z.property.2.2 (Fin.castSucc_lt_succ (i := i)))

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

/-- Erasing a selected position leaves one fewer internal mark. -/
def eraseMark {n k : ℕ} (I : Marks n (k+1)) (j : I.val) : Marks n k :=
  ⟨I.val.erase j.val, by rw [Finset.card_erase_of_mem j.property, I.property]; omega⟩

/-- Inserting an unselected position adds one internal mark. -/
def insertMark {n k : ℕ} (hk : 1 ≤ k) (I : Marks n k)
    (j : {j : Positions n // j ∉ I.val}) : Marks n (k+1) :=
  ⟨insert j.val I.val, by rw [Finset.card_insert_of_notMem j.property, I.property]; omega⟩

/-- A selected mark and its erasure correspond to a smaller selection and an unselected position. -/
def markIncidenceEquiv (n k : ℕ) (hk : 1 ≤ k) :
    (Σ I : Marks n (k+1), I.val) ≃ (Σ I : Marks n k, {j : Positions n // j ∉ I.val}) where
  toFun z := ⟨eraseMark z.1 z.2, ⟨z.2.val, Finset.notMem_erase _ _⟩⟩
  invFun z := ⟨insertMark hk z.1 z.2, ⟨z.2.val, Finset.mem_insert_self _ _⟩⟩
  left_inv z := by
    apply Sigma.ext
    · apply Subtype.ext
      exact Finset.insert_erase z.2.property
    · apply (Subtype.heq_iff_coe_eq (by
        intro t
        simp [insertMark, eraseMark, Finset.insert_erase z.2.property])).mpr
      rfl
  right_inv z := by
    apply Sigma.ext
    · apply Subtype.ext
      exact Finset.erase_insert z.2.property
    · apply (Subtype.heq_iff_coe_eq (by
        intro t
        simp [insertMark, eraseMark, z.2.property])).mpr
      rfl

/-- Omitting the chosen internal vertex of a strict divisor chain. -/
def deleteChain {n k : ℕ} (d : Chain n (k+1)) (j : Fin k) : Chain n k := by
  let e := (j.succ.castSucc).succAbove
  have hzero : e 0 = 0 := by
    apply Fin.ext
    simp [e]
  have hlast : e (Fin.last k) = Fin.last (k+1) := by
    dsimp [e]
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · exact j.isLt
  have hdiv : ∀ a b : Fin (k+2), a ≤ b → (d.val a).val ∣ (d.val b).val := by
    intro a b hab
    rcases hab.eq_or_lt with he | hlt
    · rw [he]
    · exact (Fin.liftFun_iff_succ (· ∣ ·) (f := fun i => (d.val i).val)).mpr
        (fun i => (d.property.2.2 i).1) hlt
  refine ⟨fun i => d.val (e i), ?_, ?_, ?_⟩
  · simpa only [hzero] using d.property.1
  · simpa only [hlast] using d.property.2.1
  · intro i
    have hlt := Fin.strictMono_succAbove j.succ.castSucc (Fin.castSucc_lt_succ (i := i))
    exact ⟨hdiv _ _ hlt.le,
      (Fin.strictMono_iff_lt_succ.mpr fun t => (d.property.2.2 t).2) hlt⟩
/-- Sorting the internal positions and adjoining endpoints gives increasing prefix lengths. -/
def markedRaw (n k : ℕ) (hn : 1 < n) (hk : 1 ≤ k) (z : U n k) : RawMarked n k := by
  have hlen : z.1.val.length = omegaCount n := by
    rw [omegaCount, ← ArithmeticFunction.cardFactors_eq_sum_factorization,
      ArithmeticFunction.cardFactors_apply]
    exact (Nat.primeFactorsList_unique z.1.property.2 z.1.property.1).length_eq
  have hr : 0 < omegaCount n := by
    rw [← hlen]
    exact List.length_pos_of_prod_ne_one z.1.val (by rw [z.1.property.2]; omega)
  cases k with
  | zero => omega
  | succ k =>
    let a : Fin k → ℕ := fun i =>
      (z.2.val.orderEmbOfFin (by simpa only [Nat.add_sub_cancel] using z.2.property) i).val + 1
    have ha : StrictMono a := by
      intro i j hij
      exact Nat.add_lt_add_right ((z.2.val.orderEmbOfFin _).strictMono hij) 1
    have hab : ∀ i, a i < omegaCount n := by
      intro i
      have := (z.2.val.orderEmbOfFin (by simpa only [Nat.add_sub_cancel] using z.2.property) i).isLt
      dsimp [a]
      omega
    have hs : StrictMono (Fin.snoc a (omegaCount n)) := by
      intro i j hij
      cases i using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
      | cast i =>
        cases j using Fin.lastCases with
        | last => simpa using hab i
        | cast j => simpa using ha (Fin.castSucc_lt_castSucc_iff.mp hij)
    refine ⟨(z.1, Fin.cons 0 (Fin.snoc a (omegaCount n))), ?_, ?_, ?_⟩
    · simp
    · simpa only [← Fin.succ_last, Fin.cons_succ, Fin.snoc_last] using hlen.symm
    · apply Fin.strictMono_cons.mpr
      refine ⟨?_, hs⟩
      intro j
      cases j using Fin.lastCases with
      | last => simpa using hr
      | cast j => simp [a]

/-- The sorted finite-set readout as a strict divisor chain. -/
def readoutChain (n k : ℕ) (hn : 1 < n) (hk : 1 ≤ k) (z : U n k) : Chain n k :=
  qChain (markedRaw n k hn hk z)

/-- Uniform internal-vertex deletion preserves every signed prime-word readout mass. -/
theorem actual_readout_deletion (n k : ℕ) (hn : 1 < n) (hk : 1 ≤ k)
    (hkr : k < omegaCount n) (ρ : PrimeWord n → ℝ) :
    (∀ d' : Chain n (k+1), ∑ d : Chain n k, deletionKernel n k d' d = 1) ∧
    (∀ d : Chain n k, p n k ρ (chainList d) =
      ∑ d' : Chain n (k+1), p n (k+1) ρ (chainList d') * deletionKernel n k d' d) := by
  classical
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hdelinj (d' : Chain n (k+1)) : Function.Injective (deleteChain d') := by
    intro i j hij
    have hmono := (Fin.strictMono_iff_lt_succ.mpr fun t => (d'.property.2.2 t).2)
    have he : i.succ.castSucc.succAbove = j.succ.castSucc.succAbove := by
      funext t
      apply hmono.injective
      exact congrArg (fun d : Chain n k => d.val t) hij
    have := Fin.succAbove_left_injective he
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val this))
  have hdel (d' : Chain n (k+1)) (d : Chain n k) :
      Deletes d' d ↔ ∃ j : Fin k, deleteChain d' j = d := by
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, Subtype.ext (funext fun i => Fin.ext (hj i).symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, fun _ => rfl⟩
  have hkernel (d' : Chain n (k+1)) (d : Chain n k) :
      deletionKernel n k d' d =
        ∑ j : Fin k, if deleteChain d' j = d then 1 / (k : ℝ) else 0 := by
    by_cases h : Deletes d' d
    · obtain ⟨j, rfl⟩ := (hdel d' d).mp h
      simp [deletionKernel, h, (hdelinj d').eq_iff]
    · have he : ∀ j : Fin k, deleteChain d' j ≠ d := by
        intro j hj
        exact h ((hdel d' d).mpr ⟨j, hj⟩)
      simp [deletionKernel, h, he]
  have hrow : ∀ d' : Chain n (k+1), ∑ d : Chain n k, deletionKernel n k d' d = 1 := by
    intro d'
    simp_rw [hkernel]
    rw [Finset.sum_comm]
    simp [hk0]
  have hlist (j : ℕ) (hj : 1 ≤ j) (z : U n j) :
      chainList (readoutChain n j hn hj z) = Q n j z := by
    cases j with
    | zero => omega
    | succ j =>
      dsimp [chainList, readoutChain, qChain, QNat, markedRaw, Q, qList]
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero, List.take_zero, List.prod_nil, Fin.cons_succ]
      rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have hlen : z.1.val.length = omegaCount n := by
        rw [omegaCount, ← ArithmeticFunction.cardFactors_eq_sum_factorization,
          ArithmeticFunction.cardFactors_apply]
        exact (Nat.primeFactorsList_unique z.1.property.2 z.1.property.1).length_eq
      have ht : (z.1.val.take (omegaCount n)).prod = n := by
        rw [← hlen, List.take_length, z.1.property.2]
      rw [ht]
      congr 2
      rw [← Finset.listMap_orderEmbOfFin_finRange z.2.val
        (show z.2.val.card = j by simpa only [Nat.add_sub_cancel] using z.2.property)]
      simp only [List.map_map, List.ofFn_eq_map, List.concat_eq_append, Function.comp_def]
  have hmono {j : ℕ} (c : Chain n j) : StrictMono (fun i => (c.val i).val) :=
    Fin.strictMono_iff_lt_succ.mpr fun t => (c.property.2.2 t).2
  have hrange (l : ℕ) (hl : 1 ≤ l) (z : U n l) (x : ℕ) :
      (∃ i, ((readoutChain n l hn hl z).val i).val = x) ↔
        x = 1 ∨ x = n ∨ ∃ a ∈ z.2.val, (z.1.val.take (a.val+1)).prod = x := by
    rw [← List.mem_ofFn]
    change x ∈ chainList (readoutChain n l hn hl z) ↔ _
    rw [hlist]
    simp [Q, qList, or_left_comm, or_comm, eq_comm]
  have hprefix (γ : PrimeWord n) :
      StrictMono (fun i : Fin (omegaCount n+1) => (γ.val.take i.val).prod) := by
    have hlen : γ.val.length = omegaCount n := by
      rw [omegaCount, ← ArithmeticFunction.cardFactors_eq_sum_factorization,
        ArithmeticFunction.cardFactors_apply]
      exact (Nat.primeFactorsList_unique γ.property.2 γ.property.1).length_eq
    let z : RawMarked n (omegaCount n) :=
      ⟨(γ, fun i => i.val), rfl, hlen.symm, fun _ _ h => h⟩
    exact hmono (qChain z)
  have hfactor (γ : PrimeWord n) (i : Fin (omegaCount n+1)) :
      omegaCount ((γ.val.take i.val).prod) = i.val := by
    have hlen : γ.val.length = omegaCount n := by
      rw [omegaCount, ← ArithmeticFunction.cardFactors_eq_sum_factorization,
        ArithmeticFunction.cardFactors_apply]
      exact (Nat.primeFactorsList_unique γ.property.2 γ.property.1).length_eq
    let z : RawMarked n (omegaCount n) :=
      ⟨(γ, fun i => i.val), rfl, hlen.symm, fun _ _ h => h⟩
    let c := qChain z
    have h := (snapshot_fiber_equiv_and_forced_marks n (omegaCount n)
      (fun t => (c.val t).val) hn (by omega) c.property.1 c.property.2.1 c.property.2.2).2
      ((actualChainFibreEquiv n (omegaCount n) c) ⟨z,rfl⟩) i
    exact h.symm
  have hreaddelete (γ : PrimeWord n) (I : Marks n (k+1)) (m : I.val) :
      deleteChain (readoutChain n (k+1) hn (by omega) (γ,I))
          ((I.val.orderIsoOfFin (by simpa only [Nat.add_sub_cancel] using I.property)).symm m) =
        readoutChain n k hn hk (γ, eraseMark I m) := by
    let c := readoutChain n (k+1) hn (by omega) (γ,I)
    let e := I.val.orderIsoOfFin
      (show I.val.card = k by simpa only [Nat.add_sub_cancel] using I.property)
    let j : Fin k := e.symm m
    let f : Positions n → ℕ := fun a => (γ.val.take (a.val+1)).prod
    have hf : Function.Injective f := by
      intro a b hab
      have ha := hfactor γ ⟨a.val+1, by have := a.isLt; omega⟩
      have hb := hfactor γ ⟨b.val+1, by have := b.isLt; omega⟩
      exact Fin.ext (Nat.add_right_cancel (ha.symm.trans ((congrArg omegaCount hab).trans hb)))
    have hm1 : f m.val ≠ 1 := by
      have h := hprefix γ (a := 0) (b := ⟨m.val.val+1, by have := m.val.isLt; omega⟩)
        (by exact Nat.zero_lt_succ _)
      simpa only [Fin.val_zero, List.take_zero, List.prod_nil, f] using h.ne'
    have hmn : f m.val ≠ n := by
      have hlen : γ.val.length = omegaCount n := by
        rw [omegaCount, ← ArithmeticFunction.cardFactors_eq_sum_factorization,
          ArithmeticFunction.cardFactors_apply]
        exact (Nat.primeFactorsList_unique γ.property.2 γ.property.1).length_eq
      have h := hprefix γ (a := ⟨m.val.val+1, by have := m.val.isLt; omega⟩)
        (b := Fin.last (omegaCount n)) (by
          have := m.val.isLt
          exact_mod_cast (by omega : m.val.val+1 < omegaCount n))
      have ht : (γ.val.take (omegaCount n)).prod = n := by
        rw [← hlen, List.take_length, γ.property.2]
      simpa only [Fin.val_last, ht, f] using h.ne
    have hpivot : (c.val j.succ.castSucc).val = f m.val := by
      have he : I.val.orderEmbOfFin
          (by simpa only [Nat.add_sub_cancel] using I.property) j = m.val :=
        congrArg Subtype.val (e.apply_symm_apply m)
      change (γ.val.take ((Fin.cons 0
        (Fin.snoc (fun i : Fin k =>
          (I.val.orderEmbOfFin (by simpa only [Nat.add_sub_cancel] using I.property) i).val+1)
          (omegaCount n)) : Fin (k+2) → ℕ) j.succ.castSucc)).prod = f m.val
      rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.snoc_castSucc, he]
    have hdeleted (x : ℕ) :
        (∃ i, ((deleteChain c j).val i).val = x) ↔
          (∃ i, (c.val i).val = x) ∧ x ≠ f m.val := by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨⟨j.succ.castSucc.succAbove i, hi⟩, ?_⟩
        intro hx
        exact Fin.succAbove_ne _ _ ((hmono c).injective (hi.trans (hx.trans hpivot.symm)))
      · rintro ⟨⟨i, hi⟩, hx⟩
        have hne : i ≠ j.succ.castSucc := by
          intro he
          subst i
          exact hx (hi.symm.trans hpivot)
        obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hne
        exact ⟨a, by change (c.val (j.succ.castSucc.succAbove a)).val = x; rw [ha]; exact hi⟩
    apply Subtype.ext
    have he := (hmono (deleteChain c j)).range_inj
      (hmono (readoutChain n k hn hk (γ, eraseMark I m)))
    apply funext
    intro i
    apply Fin.ext
    apply congrFun (he.mp ?_) i
    ext x
    change (∃ i, ((deleteChain c j).val i).val = x) ↔ _
    rw [hdeleted]
    change (∃ i, ((readoutChain n (k+1) hn (by omega) (γ,I)).val i).val = x) ∧
      x ≠ f m.val ↔ ∃ i, ((readoutChain n k hn hk (γ,eraseMark I m)).val i).val = x
    rw [hrange (k+1) (by omega) (γ,I) x, hrange k hk (γ,eraseMark I m) x]
    change (x = 1 ∨ x = n ∨ ∃ a ∈ I.val, f a = x) ∧ x ≠ f m.val ↔
      x = 1 ∨ x = n ∨ ∃ a ∈ I.val.erase m.val, f a = x
    by_cases hx1 : x = 1
    · subst x
      simp [hm1.symm]
    by_cases hxn : x = n
    · subst x
      simp [hmn.symm]
    simp only [hx1, hxn, false_or, Finset.mem_erase]
    constructor
    · rintro ⟨⟨a, ha, hax⟩, hx⟩
      exact ⟨a, ⟨fun ham => hx (hax.symm.trans (congrArg f ham)), ha⟩, hax⟩
    · rintro ⟨a, ⟨ham, ha⟩, hax⟩
      exact ⟨⟨a, ha, hax⟩, fun hx => ham (hf (hax.trans hx))⟩
  have hcode {l : ℕ} : Function.Injective (@chainList n l) := by
    intro a b hab
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun (List.ofFn_injective hab) i
  have hpush (l : ℕ) (hl : 1 ≤ l) (c : Chain n l) :
      p n l ρ (chainList c) = ∑ z : U n l,
        if readoutChain n l hn hl z = c then μ n l ρ z else 0 := by
    unfold p pushforward
    apply Finset.sum_congr rfl
    intro z _
    rw [← hlist l hl z, hcode.eq_iff]
  have hchoose : ((omegaCount n-1).choose k : ℝ) * (k : ℝ) =
      ((omegaCount n-1).choose (k-1) : ℝ) * (omegaCount n-k : ℕ) := by
    have h := Nat.choose_succ_right_eq (omegaCount n-1) (k-1)
    have he : k-1+1 = k := by omega
    have he' : omegaCount n-1-(k-1) = omegaCount n-k := by omega
    rw [he, he'] at h
    exact_mod_cast h
  have hc0 : ((omegaCount n-1).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ omegaCount n-1)).ne'
  have hc1 : ((omegaCount n-1).choose (k-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k-1 ≤ omegaCount n-1)).ne'
  have hratio (γ : PrimeWord n) :
      (omegaCount n-k : ℕ) * (ρ γ / ((omegaCount n-1).choose k : ℝ) * (1/(k : ℝ))) =
        ρ γ / ((omegaCount n-1).choose (k-1) : ℝ) := by
    field_simp
    nlinarith only [congrArg (fun t : ℝ => ρ γ * t) hchoose]
  refine ⟨hrow, ?_⟩
  intro d
  have htransport :
      (∑ c : Chain n (k+1), p n (k+1) ρ (chainList c) * deletionKernel n k c d) =
        ∑ z : U n (k+1), μ n (k+1) ρ z *
          deletionKernel n k (readoutChain n (k+1) hn (by omega) z) d := by
    have h := sum_indicator_comp
      (fun z : U n (k+1) => μ n (k+1) ρ z *
        deletionKernel n k (readoutChain n (k+1) hn (by omega) z) d)
      (readoutChain n (k+1) hn (by omega)) (fun _ : Chain n (k+1) => ()) ()
    simp only [ite_true] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro c _
    rw [hpush (k+1) (by omega), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs with he
    · rw [he]
    · simp
  rw [htransport, hpush k hk]
  change (∑ z : PrimeWord n × Marks n k, _) = (∑ z : PrimeWord n × Marks n (k+1), _)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro γ _
  symm
  calc
    _ = ∑ I : Marks n (k+1), ∑ m : I.val,
          if readoutChain n k hn hk (γ, eraseMark I m) = d then
            ρ γ / ((omegaCount n-1).choose k : ℝ) * (1/(k : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro I _
      rw [hkernel, Finset.mul_sum]
      simp only [μ, Nat.add_sub_cancel, mul_ite, mul_zero]
      let e := (I.val.orderIsoOfFin
        (show I.val.card = k by simpa only [Nat.add_sub_cancel] using I.property)).toEquiv
      apply Fintype.sum_equiv e
      intro j
      have h := hreaddelete γ I (e j)
      simpa [e] using
        congrArg (fun c : Chain n k => if c = d then
          ρ γ / ((omegaCount n-1).choose k : ℝ) * (1/(k : ℝ)) else 0) h
    _ = ∑ z : (Σ I : Marks n (k+1), I.val),
          if readoutChain n k hn hk (γ, eraseMark z.1 z.2) = d then
            ρ γ / ((omegaCount n-1).choose k : ℝ) * (1/(k : ℝ)) else 0 := by
      rw [Fintype.sum_sigma]
    _ = ∑ z : (Σ I : Marks n k, {a : Positions n // a ∉ I.val}),
          if readoutChain n k hn hk (γ, z.1) = d then
            ρ γ / ((omegaCount n-1).choose k : ℝ) * (1/(k : ℝ)) else 0 := by
      exact Fintype.sum_equiv (markIncidenceEquiv n k hk) _ _ (fun _ => rfl)
    _ = ∑ I : Marks n k, if readoutChain n k hn hk (γ,I) = d then μ n k ρ (γ,I) else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro I _
      have hcard : Fintype.card {a : Positions n // a ∉ I.val} = omegaCount n-k := by
        rw [Fintype.card_subtype_compl]
        simp only [Fintype.card_fin, Fintype.card_coe, I.property, Positions]
        omega
      split_ifs
      · simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, μ] using hratio γ
      · simp

#print axioms actual_readout_deletion
end D5.S3.Factorization.Combinatorics.MarkedPrimeWordReadoutDeletion
