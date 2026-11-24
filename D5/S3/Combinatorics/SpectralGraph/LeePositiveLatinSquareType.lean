/- GID: D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.claim; result=D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.result; claim=D5/S3/Combinatorics/SpectralGraph/LeePositiveLatinSquareType.claim
   digest: The binary symmetric rank-distance graph at dimension seven and threshold five fails the positive Latin-square-type valency. -/

import D5.S1.Digit.GoldenBase4ResidueBridge
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.SpectralGraph.LeePositiveLatinSquareType

private def SymmetricMatrix (K : Type) (m : ℕ) :=
  {A : Matrix (Fin m) (Fin m) K // ∀ i j, A i j = A j i}

private instance {K : Type} [Finite K] (m : ℕ) : Finite (SymmetricMatrix K m) :=
  inferInstanceAs (Finite {A : Matrix (Fin m) (Fin m) K // ∀ i j, A i j = A j i})

private theorem rank_neg {K : Type} [Field K] {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    (-A).rank = A.rank := by
  rw [← neg_one_smul K A]
  exact A.rank_smul_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero (by simp))

private def rankGraph (K : Type) [Field K] (m d : ℕ) :
    SimpleGraph (SymmetricMatrix K m) where
  Adj A B := A ≠ B ∧ d ≤ (A.val - B.val).rank
  symm := ⟨by
    intro A B h
    refine ⟨h.1.symm, ?_⟩
    rw [← neg_sub A.val B.val, rank_neg]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private noncomputable def positiveLatinSquareType {V : Type} [Finite V]
    (G : SimpleGraph V) : Prop :=
  letI : Fintype V := Fintype.ofFinite V
  letI (A : V) : Fintype (G.neighborSet A) := Fintype.ofFinite _
  ∃ n t : ℕ, 0 < n ∧ 0 < t ∧ Fintype.card V = n ^ 2 ∧
    (∀ A, G.degree A = t * (n - 1)) ∧
    ∀ eigenvalue : ℝ, (eigenvalue = (n : ℝ) - (t : ℝ) ∨ eigenvalue = -(t : ℝ)) ↔
      ∃ f : V → ℝ, f ≠ 0 ∧ (∑ A, f A) = 0 ∧
        ∀ A, (∑ B ∈ G.neighborFinset A, f B) = eigenvalue * f A

/-- Lee's question for both dimension classes and every finite field. -/
def claim : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (m d : ℕ), 0 < m →
    ((m % 4 = 3 ∧ d = (m + 3) / 2) ∨ (m % 4 = 0 ∧ d = (m + 2) / 2)) →
    positiveLatinSquareType (rankGraph K m d)

private abbrev Binary := ZMod 2
private abbrev Vertex := SymmetricMatrix Binary 7

private abbrev UpperTriangle := {ij : Fin 7 × Fin 7 // ij.1 ≤ ij.2}

private def upperTriangleEquiv : Vertex ≃ (UpperTriangle → Binary) where
  toFun A p := A.val p.val.1 p.val.2
  invFun f := ⟨fun i j =>
    if h : i ≤ j then f ⟨(i, j), h⟩ else f ⟨(j, i), (le_of_not_ge h)⟩, by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hji
      · simp [hij.le, not_le_of_gt hij]
      · rfl
      · simp [hji.le, not_le_of_gt hji]⟩
  left_inv := by
    intro A
    apply Subtype.ext
    ext i j
    change (if h : i ≤ j then A.val i j else A.val j i) = A.val i j
    split
    · rfl
    · exact A.property j i
  right_inv := by
    intro f
    funext p
    exact dite_eq_left p.property

private noncomputable def upperCoordinates : UpperTriangle ≃ Fin 28 :=
  Fintype.equivFinOfCardEq (by decide)

private noncomputable def vertexCoordinates : Vertex ≃ (Fin 28 → Binary) :=
  upperTriangleEquiv.trans (Equiv.arrowCongr upperCoordinates (Equiv.refl Binary))

private theorem vertex_card : Nat.card Vertex = 268435456 := by
  rw [Nat.card_congr vertexCoordinates, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]
  decide

private theorem square_order {n : ℕ} (hn : Nat.card Vertex = n ^ 2) : n = 16384 := by
  apply Nat.pow_left_injective (show 2 ≠ 0 by decide)
  change n ^ 2 = 16384 ^ 2
  rw [← hn, vertex_card]

private def zeroVertex : Vertex :=
  ⟨0, fun _ _ => rfl⟩

private abbrev binaryGraph : SimpleGraph Vertex := rankGraph Binary 7 5
private abbrev ZeroNeighbor := binaryGraph.neighborSet zeroVertex

private theorem zero_adj_iff (A : Vertex) : binaryGraph.Adj zeroVertex A ↔ 5 ≤ A.val.rank := by
  change (zeroVertex ≠ A ∧ 5 ≤ ((0 : Matrix (Fin 7) (Fin 7) Binary) - A.val).rank) ↔ _
  rw [zero_sub, rank_neg]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  change 5 ≤ (0 : Matrix (Fin 7) (Fin 7) Binary).rank at h
  rw [Matrix.rank_zero] at h
  omega

private def rotate : Equiv.Perm (Fin 7) where
  toFun i := ![1, 2, 0, 4, 5, 3, 6] i
  invFun i := ![2, 0, 1, 5, 3, 4, 6] i
  left_inv := by decide
  right_inv := by decide

private theorem rotate_cube : ∀ i, rotate (rotate (rotate i)) = i := by decide

private def relabel (A : Vertex) : Vertex :=
  ⟨A.val.submatrix rotate rotate, fun i j => A.property (rotate i) (rotate j)⟩

private theorem relabel_rank (A : Vertex) : (relabel A).val.rank = A.val.rank :=
  Matrix.rank_submatrix A.val rotate rotate

private def step (A : ZeroNeighbor) : ZeroNeighbor :=
  ⟨relabel A.val, (zero_adj_iff _).2 (by
    rw [relabel_rank]
    exact (zero_adj_iff _).1 A.property)⟩

private theorem step_cube (A : ZeroNeighbor) : step (step (step A)) = A := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change A.val.val (rotate (rotate (rotate i))) (rotate (rotate (rotate j))) = A.val.val i j
  rw [rotate_cube, rotate_cube]

private def zeroPerm : Equiv.Perm ZeroNeighbor where
  toFun := step
  invFun A := step (step A)
  left_inv := step_cube
  right_inv := step_cube

private def zeroEnd : Function.End ZeroNeighbor := fun A => zeroPerm A

private theorem zeroPerm_order : orderOf zeroPerm = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Equiv.ext
    intro A
    exact step_cube A
  · intro heq
    let diagonal : Fin 7 → Binary := ![0, 1, 1, 1, 1, 1, 1]
    let A : Vertex := ⟨Matrix.diagonal diagonal, fun i j => by
      by_cases h : i = j
      · subst j
        rfl
      · simp [h, Ne.symm h]⟩
    have hrank : 5 ≤ A.val.rank := by
      change 5 ≤ (Matrix.diagonal diagonal).rank
      rw [Matrix.rank_diagonal]
      decide
    let U : ZeroNeighbor := ⟨A, (zero_adj_iff A).2 hrank⟩
    have h := congrArg (fun e : Equiv.Perm ZeroNeighbor => (e U).val.val 0 0) heq
    change (1 : Binary) = 0 at h
    exact one_ne_zero h

private theorem step_pow : zeroEnd ^ (3 ^ 1 : ℕ) = 1 := by
  have h := pow_orderOf_eq_one zeroPerm
  rw [zeroPerm_order] at h
  funext A
  exact congrArg (fun e : Equiv.Perm ZeroNeighbor => e A) h

private theorem neighbor_fixed_congruence :
    Nat.card ZeroNeighbor ≡ Nat.card (Function.fixedPoints zeroEnd) [MOD 3] := by
  classical
  let : Fintype ZeroNeighbor := Fintype.ofFinite _
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  simpa only [Fintype.card_eq_nat_card] using Equiv.Perm.card_fixedPoints_modEq step_pow

private def orbitClass (i j : Fin 7) : Fin 10 :=
  ![![0, 1, 1, 2, 3, 4, 5],
    ![1, 0, 1, 4, 2, 3, 5],
    ![1, 1, 0, 3, 4, 2, 5],
    ![2, 4, 3, 6, 7, 7, 8],
    ![3, 2, 4, 7, 6, 7, 8],
    ![4, 3, 2, 7, 7, 6, 8],
    ![5, 5, 5, 8, 8, 8, 9]] i j

private def representative (c : Fin 10) : Fin 7 × Fin 7 :=
  ![(0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (3, 3), (3, 4), (3, 6), (6, 6)] c

private theorem class_symmetric : ∀ i j, orbitClass j i = orbitClass i j := by decide

private theorem class_invariant : ∀ i j, orbitClass (rotate i) (rotate j) = orbitClass i j := by
  decide

private theorem class_representative :
    ∀ c, orbitClass (representative c).1 (representative c).2 = c := by decide

private def rotatePair (p : Fin 7 × Fin 7) : Fin 7 × Fin 7 :=
  (rotate p.1, rotate p.2)

private theorem pair_reachable : ∀ i j,
    ∃ k : Fin 3, (rotatePair^[k.val]) (representative (orbitClass i j)) = (i, j) ∨
      (rotatePair^[k.val]) (representative (orbitClass i j)) = (j, i) := by decide

private def fromClasses (bits : Fin 10 → Binary) : Vertex :=
  ⟨fun i j => bits (orbitClass i j), fun i j => congrArg bits (class_symmetric i j).symm⟩

private abbrev FixedVertex := {A : Vertex // relabel A = A}

private theorem fromClasses_fixed (bits : Fin 10 → Binary) :
    relabel (fromClasses bits) = fromClasses bits := by
  apply Subtype.ext
  ext i j
  exact congrArg bits (class_invariant i j)

private theorem fixed_entry (A : FixedVertex) (i j : Fin 7) :
    A.val.val i j =
      A.val.val (representative (orbitClass i j)).1 (representative (orbitClass i j)).2 := by
  let entry (p : Fin 7 × Fin 7) := A.val.val p.1 p.2
  have hstep (p : Fin 7 × Fin 7) : entry (rotatePair p) = entry p :=
    congrArg (fun B : Vertex => B.val p.1 p.2) A.property
  have hiter (k : ℕ) (p : Fin 7 × Fin 7) : entry ((rotatePair^[k]) p) = entry p := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hstep, ih]
  obtain ⟨k, h | h⟩ := pair_reachable i j
  · simpa only [h] using hiter k.val (representative (orbitClass i j))
  · rw [A.val.property i j]
    simpa only [h] using hiter k.val (representative (orbitClass i j))

private def classesEquiv : (Fin 10 → Binary) ≃ FixedVertex where
  toFun bits := ⟨fromClasses bits, fromClasses_fixed bits⟩
  invFun A c := A.val.val (representative c).1 (representative c).2
  left_inv bits := by
    funext c
    exact congrArg bits (class_representative c)
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    exact (fixed_entry A i j).symm

private def binaryDigits (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Binary) :=
  finFunctionFinEquiv.symm.trans
    (Equiv.arrowCongr (Equiv.refl (Fin n)) (ZMod.finEquiv 2).toEquiv)

private abbrev Mask := Fin 1024

private def maskEquiv : Mask ≃ FixedVertex :=
  (binaryDigits 10).trans classesEquiv

private def maskMatrix (a : Mask) : Matrix (Fin 7) (Fin 7) Binary :=
  (maskEquiv a).val.val

private def fixedNeighborsEquiv :
    Function.fixedPoints zeroEnd ≃ {A : FixedVertex // 5 ≤ A.val.val.rank} where
  toFun A := ⟨⟨A.val.val, congrArg Subtype.val A.property⟩, (zero_adj_iff _).1 A.val.property⟩
  invFun A := ⟨⟨A.val.val, (zero_adj_iff _).2 A.property⟩, Subtype.ext A.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def vectorDigits : Fin 128 ≃ (Fin 7 → Binary) := binaryDigits 7

/-- In the binary field, the dot product is the parity of the entrywise products. -/
private def rowParity (a : Mask) (x : Fin 128) (i : Fin 7) : Binary :=
  maskMatrix a i 0 * vectorDigits x 0 +
  maskMatrix a i 1 * vectorDigits x 1 +
  maskMatrix a i 2 * vectorDigits x 2 +
  maskMatrix a i 3 * vectorDigits x 3 +
  maskMatrix a i 4 * vectorDigits x 4 +
  maskMatrix a i 5 * vectorDigits x 5 +
  maskMatrix a i 6 * vectorDigits x 6

private theorem rowParity_correct (a : Mask) (x : Fin 128) (i : Fin 7) :
    rowParity a x i = ((maskMatrix a).mulVecLin (vectorDigits x)) i := by
  simp only [rowParity, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  change _ = maskMatrix a i 0 * vectorDigits x 0 +
    (maskMatrix a i 1 * vectorDigits x 1 +
    (maskMatrix a i 2 * vectorDigits x 2 +
    (maskMatrix a i 3 * vectorDigits x 3 +
    (maskMatrix a i 4 * vectorDigits x 4 +
    (maskMatrix a i 5 * vectorDigits x 5 + maskMatrix a i 6 * vectorDigits x 6)))))
  ac_rfl

private def inKernel (a : Mask) (x : Fin 128) : Bool :=
  (List.finRange 7).all fun i => decide (rowParity a x i = 0)

private theorem inKernel_iff (a : Mask) (x : Fin 128) :
    inKernel a x = true ↔ vectorDigits x ∈ LinearMap.ker (maskMatrix a).mulVecLin := by
  simp only [inKernel, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
    rowParity_correct, LinearMap.mem_ker, funext_iff, Pi.zero_apply]

private def kernelCount (a : Mask) : ℕ :=
  (List.finRange 128).countP (inKernel a)

private def kernelEquiv (a : Mask) :
    {x : Fin 128 // inKernel a x = true} ≃ LinearMap.ker (maskMatrix a).mulVecLin :=
  vectorDigits.subtypeEquiv (inKernel_iff a)

private theorem kernelCount_correct (a : Mask) :
    kernelCount a = Nat.card (LinearMap.ker (maskMatrix a).mulVecLin) := by
  rw [← Nat.card_congr (kernelEquiv a), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have huniv : (List.finRange 128).toFinset = (Finset.univ : Finset (Fin 128)) := by
    ext x
    simp
  rw [← huniv]
  exact (List.Nodup.card_eq_countP (P := fun x => inKernel a x = true) (List.nodup_finRange 128)).symm

private def rankTest (a : Mask) : Bool := decide (kernelCount a ≤ 4)

private theorem rankTest_iff (a : Mask) : rankTest a = true ↔ 5 ≤ (maskMatrix a).rank := by
  classical
  let f := (maskMatrix a).mulVecLin
  have hnull := f.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hnull
  have hrank : (maskMatrix a).rank = Module.finrank Binary f.range := rfl
  have hcard : Nat.card f.ker = 2 ^ Module.finrank Binary f.ker := by
    rw [Module.natCard_eq_pow_finrank (K := Binary), Nat.card_eq_fintype_card, ZMod.card]
  rw [rankTest, decide_eq_true_eq, kernelCount_correct, hrank, hcard]
  have hpow : 2 ^ Module.finrank Binary f.ker ≤ 2 ^ 2 ↔ Module.finrank Binary f.ker ≤ 2 :=
    Nat.pow_le_pow_iff_right (by decide)
  change 2 ^ Module.finrank Binary f.ker ≤ 2 ^ 2 ↔ _
  rw [hpow]
  omega

private def chunkMask : Fin 32 × Fin 32 ≃ Mask := finProdFinEquiv

private def chunkCount (c : Fin 32) : ℕ :=
  (List.finRange 32).countP fun i => rankTest (chunkMask (c, i))


private def expectedChunk : Fin 32 → ℕ :=
  ![18, 24, 16, 32, 12, 16, 24, 28,
    26, 26, 24, 24, 24, 24, 26, 26,
    26, 26, 24, 24, 24, 24, 26, 26,
    26, 26, 24, 24, 24, 24, 26, 26]

set_option maxHeartbeats 0 in
/-- Each invocation of the kernel checks only the 32 masks in one chunk. -/
private theorem chunk_counts (c : Fin 32) : chunkCount c = expectedChunk c := by
  fin_cases c <;> decide +kernel

private abbrev AcceptedMask := {a : Mask // rankTest a = true}

private abbrev AcceptedOffset (c : Fin 32) :=
  {i : Fin 32 // rankTest (chunkMask (c, i)) = true}

/-- Quotient and remainder locate each mask in exactly one contiguous chunk. -/
private def chunkEquiv : (Σ c : Fin 32, AcceptedOffset c) ≃ AcceptedMask :=
  (show (Σ c : Fin 32, AcceptedOffset c) ≃
      {p : Fin 32 × Fin 32 // rankTest (chunkMask p) = true} from
    { toFun := fun ⟨c, i⟩ => ⟨(c, i.val), i.property⟩
      invFun := fun ⟨p, h⟩ => ⟨p.1, p.2, h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (chunkMask.subtypeEquiv fun _ => Iff.rfl)

private theorem card_offset (c : Fin 32) : Fintype.card (AcceptedOffset c) = chunkCount c := by
  rw [Fintype.card_subtype]
  have huniv : (List.finRange 32).toFinset = (Finset.univ : Finset (Fin 32)) := by
    ext i
    simp
  rw [← huniv]
  exact List.Nodup.card_eq_countP (List.nodup_finRange 32)

private theorem accepted_card : Nat.card AcceptedMask = 770 := by
  rw [← Nat.card_congr chunkEquiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [card_offset, chunk_counts]
  decide

private def acceptedEquiv : AcceptedMask ≃ Function.fixedPoints zeroEnd :=
  (maskEquiv.subtypeEquiv rankTest_iff).trans fixedNeighborsEquiv.symm

private theorem fixed_count : Nat.card (Function.fixedPoints zeroEnd) = 770 :=
  (Nat.card_congr acceptedEquiv).symm.trans accepted_card

private theorem degree_residue : Nat.card ZeroNeighbor % 3 = 2 := by
  have h := neighbor_fixed_congruence
  rw [fixed_count] at h
  exact h

/-- Lee's positive Latin-square-type claim fails at the binary rank-five graph. -/
theorem result : ¬ claim := by
  intro h
  have hw := h Binary 7 5 (by decide) (Or.inl ⟨by decide, by decide⟩)
  obtain ⟨n, t, _, _, hsize, hvalency, _⟩ := hw
  have hsize' : Nat.card Vertex = n ^ 2 := (Fintype.card_eq_nat_card).symm.trans hsize
  have hn := square_order hsize'
  have hcast : (n : ZMod 3) = ((1 : ℕ) : ZMod 3) := by
    have hn' : n = 4 ^ 7 := hn
    rw [hn', Nat.cast_pow, Nat.cast_ofNat]
    exact D5.S1.Digit.GoldenBase4ResidueBridge.four_pow_mod_three 7
  have hrem : n % 3 = 1 := (ZMod.natCast_eq_natCast_iff' n 1 3).1 hcast
  have hfactor : n - 1 = 3 * (n / 3) := by
    have hdiv := Nat.mod_add_div n 3
    rw [hrem] at hdiv
    calc
      n - 1 = (1 + 3 * (n / 3)) - 1 := congrArg (fun k : ℕ => k - 1) hdiv.symm
      _ = 3 * (n / 3) := Nat.add_sub_cancel_left 1 _
  let : Fintype ZeroNeighbor := Fintype.ofFinite _
  have hdegree : Nat.card ZeroNeighbor = t * (n - 1) :=
    Fintype.card_eq_nat_card.symm.trans ((binaryGraph.card_neighborSet_eq_degree zeroVertex).trans
      (hvalency zeroVertex))
  have hbad := degree_residue
  rw [hdegree, hfactor, Nat.mul_left_comm, Nat.mul_mod_right] at hbad
  contradiction

end D5.S3.Combinatorics.SpectralGraph.LeePositiveLatinSquareType
