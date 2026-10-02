/- GID: D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation.claim; result=D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation.result; claim=D5/S0/Certificates/Combinatorics/OkadaDiscriminantRefutation.claim
   digest: The Okada regular-trace discriminant is -16 while the cell product is 1 at rank 3. -/

/-
proof_shape: result: content (rank-three quotient basis, regular trace and cell-form computation).
  Private rank3_basis_exists: content (span induction and explicit model proving independence).
escape_witness: rank3_basis_exists, on the live path computing the regular trace and cell forms.
admission_basis: open-problem-resolution (#11538; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.Trace


namespace D5.S0.Certificates.Combinatorics.OkadaDiscriminantRefutation
set_option maxSynthPendingDepth 64
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
open Matrix Module
noncomputable section

variable (N : ℕ) (𝕂 : Type) [Field 𝕂]

inductive Relations (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) :
    FreeAlgebra 𝕂 (Fin (N-1)) → FreeAlgebra 𝕂 (Fin (N-1)) → Prop
  | square (i) : Relations X Y
      (FreeAlgebra.ι 𝕂 i * FreeAlgebra.ι 𝕂 i)
      (X i • FreeAlgebra.ι 𝕂 i)
  | commute (i j) (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
      Relations X Y (FreeAlgebra.ι 𝕂 i * FreeAlgebra.ι 𝕂 j)
        (FreeAlgebra.ι 𝕂 j * FreeAlgebra.ι 𝕂 i)
  | sandwich (i : Fin (N-2)) (h : i.val + 1 < N-1) :
      Relations X Y
        (FreeAlgebra.ι 𝕂 ⟨i.val+1,h⟩ * FreeAlgebra.ι 𝕂 ⟨i.val,by omega⟩ *
          FreeAlgebra.ι 𝕂 ⟨i.val+1,h⟩)
        (Y i • FreeAlgebra.ι 𝕂 ⟨i.val+1,h⟩)

abbrev Presented (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) :=
  RingQuot (Relations N 𝕂 X Y)

def generator (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) (i : Fin (N-1)) :
    Presented N 𝕂 X Y :=
  RingQuot.mkAlgHom 𝕂 (Relations N 𝕂 X Y) (FreeAlgebra.ι 𝕂 i)

def code (σ : Equiv.Perm (Fin N)) (i : Fin N) : ℕ :=
  ((Finset.univ.filter fun k => k < i ∧ σ.symm i < σ.symm k)).card

-- The list i-1,i-2,...,i-c_i in paper indices is i-1,i-2,...,i-c_i
-- in zero-based generator indices when i itself is zero based.
def lexmin (σ : Equiv.Perm (Fin N)) : List (Fin (N-1)) :=
  (List.finRange N).flatMap fun i =>
    ((List.finRange i.val).reverse.filter fun j => i.val - code N σ i ≤ j.val).map
      fun j => ⟨j.val,by omega⟩

def lexElement (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂)
    (σ : Equiv.Perm (Fin N)) : Presented N 𝕂 X Y :=
  ((lexmin N σ).map (generator N 𝕂 X Y)).prod

def regularGram (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) :
    Matrix (Equiv.Perm (Fin N)) (Equiv.Perm (Fin N)) 𝕂 :=
  fun σ τ => LinearMap.trace 𝕂 (Presented N 𝕂 X Y)
    (Algebra.lmul 𝕂 _ (lexElement N 𝕂 X Y σ) *
      Algebra.lmul 𝕂 _ (lexElement N 𝕂 X Y τ))

-- A sorted finite subset; the count of smaller entries is the zero-based index
-- in the increasing enumeration used in Definition 4.5 (def:fibonacci-sets).
abbrev IsFibonacciSet (S : Finset (Fin N)) : Prop :=
  S.card % 2 = N % 2 ∧
    ∀ s ∈ S, (s.val+1) % 2 = (((S.filter fun t => t < s).card)+1) % 2

abbrev FibonacciSet := { S : Finset (Fin N) // IsFibonacciSet N S }

-- Rank-three witness parameters, retaining the actual presented quotient.
private def witnessX : Fin 2 → ℚ := ![1,2]
private def witnessY : Fin 1 → ℚ := ![1]
private abbrev Q3 := Presented 3 ℚ witnessX witnessY

private def a : Q3 := generator 3 ℚ witnessX witnessY 0
private def b : Q3 := generator 3 ℚ witnessX witnessY 1

private def sixWords : Fin 6 → Q3 := ![1,a,b,a*b,b*a,a*b*a]
private abbrev Model := ℚ × ℚ × Matrix (Fin 2) (Fin 2) ℚ

private def modelA : Model := (0,1,!![1,0;0,0])
private def modelB : Model := (0,0,!![1,1;1,1])
private def modelWords (i : Fin 6) : Model :=
  match i.val with
  | 0 => 1
  | 1 => modelA
  | 2 => modelB
  | 3 => modelA*modelB
  | 4 => modelB*modelA
  | _ => modelA*modelB*modelA


private def modelCoordinates : Model ≃ₗ[ℚ] (Fin 6 → ℚ) where
  toFun z i := match i.val with
    | 0 => z.1
    | 1 => z.2.1-z.1
    | 2 => z.2.2 1 1-z.1
    | 3 => z.2.2 0 1-z.2.2 1 1+z.1
    | 4 => z.2.2 1 0-z.2.2 1 1+z.1
    | _ => z.2.2 0 0-z.2.1-z.2.2 0 1-z.2.2 1 0+z.2.2 1 1-z.1
  invFun c := ∑ i, c i • modelWords i
  left_inv z := by
    ext i j <;> (try fin_cases i) <;> (try fin_cases j) <;> simp [modelWords, modelA, modelB, Fin.sum_univ_succ,
      Matrix.mul_apply, Matrix.one_apply] <;> ring
  right_inv c := by
    ext i
    fin_cases i <;> simp [modelWords, modelA, modelB, Fin.sum_univ_succ,
      Matrix.mul_apply, Matrix.one_apply] <;> ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    ext i
    fin_cases i <;> simp <;> ring

private def modelHom : Q3 →ₐ[ℚ] Model :=
  RingQuot.liftAlgHom ℚ ⟨FreeAlgebra.lift ℚ ![modelA,modelB],by
    intro x y h
    cases h with
    | square i =>
      simp only [map_mul, map_smul, FreeAlgebra.lift_ι_apply]
      fin_cases i
      · change modelA * modelA = (1:ℚ) • modelA
        ext i j <;> (try fin_cases i) <;> (try fin_cases j) <;>
          norm_num [modelA, Matrix.mul_apply, Fin.sum_univ_succ]
      · change modelB * modelB = (2:ℚ) • modelB
        ext i j <;> (try fin_cases i) <;> (try fin_cases j) <;>
          norm_num [modelB, Matrix.mul_apply, Fin.sum_univ_succ]
    | commute i j h =>
      have hi := i.isLt
      have hj := j.isLt
      omega
    | sandwich i h =>
      simp only [map_mul, map_smul, FreeAlgebra.lift_ι_apply]
      fin_cases i
      change modelB * modelA * modelB = (1:ℚ) • modelB
      ext i j <;> (try fin_cases i) <;> (try fin_cases j) <;>
        norm_num [modelA, modelB, Matrix.mul_apply, Fin.sum_univ_succ]⟩

private theorem rank3_basis_exists : ∃ B : Basis (Fin 6) ℚ Q3, ∀ i, B i = sixWords i := by
  classical
  let q : FreeAlgebra ℚ (Fin 2) →ₐ[ℚ] Q3 := RingQuot.mkAlgHom ℚ (Relations 3 ℚ witnessX witnessY)
  have aa : a*a = a := by
    have h : q (FreeAlgebra.ι ℚ 0 * FreeAlgebra.ι ℚ 0) =
        q (witnessX 0 • FreeAlgebra.ι ℚ 0) := RingQuot.mkAlgHom_rel ℚ
      (Relations.square (N:=3) (𝕂:=ℚ) (X:=witnessX) (Y:=witnessY) (0:Fin 2))
    rw [map_mul q,map_smul q] at h
    change a*a = (1:ℚ) • a at h
    simpa only [one_smul] using h
  have bb : b*b = (2:ℚ) • b := by
    have h : q (FreeAlgebra.ι ℚ 1 * FreeAlgebra.ι ℚ 1) =
        q (witnessX 1 • FreeAlgebra.ι ℚ 1) := RingQuot.mkAlgHom_rel ℚ
      (Relations.square (N:=3) (𝕂:=ℚ) (X:=witnessX) (Y:=witnessY) (1:Fin 2))
    rw [map_mul q,map_smul q] at h
    change b*b = (2:ℚ) • b at h
    exact h
  have bab : b*a*b = b := by
    have h : q (FreeAlgebra.ι ℚ 1 * FreeAlgebra.ι ℚ 0 * FreeAlgebra.ι ℚ 1) =
        q (witnessY 0 • FreeAlgebra.ι ℚ 1) := RingQuot.mkAlgHom_rel ℚ
      (Relations.sandwich (N:=3) (𝕂:=ℚ) (X:=witnessX) (Y:=witnessY) (0:Fin 1) (by decide))
    rw [map_mul q,map_mul q,map_smul q] at h
    change b*a*b = (1:ℚ) • b at h
    simpa only [one_smul] using h
  let S := Submodule.span ℚ (Set.range sixWords)
  have wmem : ∀ i, sixWords i ∈ S := fun i => Submodule.subset_span ⟨i,rfl⟩
  have stableA : ∀ z ∈ S, a*z ∈ S := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨i,rfl⟩
      fin_cases i
      · simpa [sixWords] using wmem 1
      · simpa [sixWords,aa] using wmem 1
      · simpa [sixWords] using wmem 3
      · simpa [sixWords,←mul_assoc,aa] using wmem 3
      · simpa [sixWords,mul_assoc] using wmem 5
      · simpa [sixWords,←mul_assoc,aa] using wmem 5
    | zero => simp
    | add x y hx hy px py => simpa [mul_add] using S.add_mem px py
    | smul r x hx px => simpa [mul_smul_comm] using S.smul_mem r px
  have stableB : ∀ z ∈ S, b*z ∈ S := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      rcases hw with ⟨i,rfl⟩
      fin_cases i
      · simpa [sixWords] using wmem 2
      · simpa [sixWords] using wmem 4
      · simpa [sixWords,bb] using S.smul_mem (2:ℚ) (wmem 2)
      · simpa [sixWords,←mul_assoc,bab] using wmem 2
      · simpa [sixWords,←mul_assoc,bb,smul_mul_assoc] using S.smul_mem (2:ℚ) (wmem 4)
      · simpa [sixWords,←mul_assoc,bab] using wmem 4
    | zero => simp
    | add x y hx hy px py => simpa [mul_add] using S.add_mem px py
    | smul r x hx px => simpa [mul_smul_comm] using S.smul_mem r px
  have pres : ∀ f : FreeAlgebra ℚ (Fin 2), ∀ z ∈ S, q f*z ∈ S := by
    intro f
    induction f using FreeAlgebra.induction with
    | grade0 r =>
      intro z hz
      simpa [q,Algebra.algebraMap_eq_smul_one] using S.smul_mem r hz
    | grade1 i =>
      fin_cases i
      · exact stableA
      · exact stableB
    | mul f g pf pg =>
      intro z hz
      simpa only [map_mul,mul_assoc] using pf (q g*z) (pg z hz)
    | add f g pf pg =>
      intro z hz
      simpa only [map_add,add_mul] using S.add_mem (pf z hz) (pg z hz)
  have spanning : S = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨f,rfl⟩ := RingQuot.mkAlgHom_surjective ℚ (Relations 3 ℚ witnessX witnessY) z
    simpa [q,sixWords] using pres f 1 (by simpa [sixWords] using wmem 0)
  have hwords : ∀ i, modelHom (sixWords i) = modelWords i := by
    have ha : modelHom a = modelA := by
      unfold modelHom a generator
      rw [RingQuot.liftAlgHom_mkAlgHom_apply]
      simp
    have hb : modelHom b = modelB := by
      unfold modelHom b generator
      rw [RingQuot.liftAlgHom_mkAlgHom_apply]
      simp
    intro i
    fin_cases i <;> simp [sixWords,modelWords,ha,hb]
  let BM : Basis (Fin 6) ℚ Model := (Pi.basisFun ℚ (Fin 6)).map modelCoordinates.symm
  have bmwords : ∀ i, BM i = modelWords i := by
    intro i
    fin_cases i <;>
      simp [BM, Basis.map_apply, Pi.basisFun_apply, modelCoordinates, Fin.sum_univ_succ]
  have independent : LinearIndependent ℚ sixWords := by
    apply LinearIndependent.of_comp modelHom.toLinearMap
    have heq : modelHom.toLinearMap ∘ sixWords = BM := by
      funext i
      exact (hwords i).trans (bmwords i).symm
    rw [heq]
    exact BM.linearIndependent
  refine ⟨Basis.mk independent (by simpa [S,spanning]), ?_⟩
  intro i
  exact Basis.mk_apply _ _ i

/- Half diagrams store a partial matching as an involution: fixed points are
propagating endpoints. Labels are zero based. Isotopies are quotiented by
storing incidence alone, as the paper instructs. -/
abbrev HalfData (N : ℕ) := (Fin N → Fin N) × (Fin N → Fin N)

abbrev HalfValid (H : HalfData N) : Prop :=
  (∀ i, H.1 (H.1 i) = i) ∧
  (∀ i, H.2 (H.1 i) = H.2 i) ∧
  (∀ i, H.2 i ≤ i ∧ (H.2 i).val % 2 = (min i (H.1 i)).val % 2) ∧
  (∀ i j, i < H.1 i → H.1 j = j → ¬ (i < j ∧ j < H.1 i)) ∧
  (∀ i j, i < H.1 i → j < H.1 j → i < j → j < H.1 i → H.1 j < H.1 i) ∧
  (∀ i j, i < H.1 i → j < H.1 j → i < j → H.1 j < H.1 i → H.2 i < H.2 j) ∧
  (∀ i j, H.1 i = i → j < H.1 j → i < j → H.2 i < H.2 j) ∧
  (∀ i j, H.1 i = i → H.1 j = j → i < j → H.2 i < H.2 j)

abbrev HalfDiagram (N : ℕ) := { H : HalfData N // HalfValid N H }

def propagatingIndices (H : HalfDiagram N) : Finset (Fin N) :=
  Finset.univ.filter fun i => H.val.1 i = i

def propagatingLabels (H : HalfDiagram N) : Finset (Fin N) :=
  (propagatingIndices N H).image H.val.2

abbrev Diagram (N : ℕ) := { HK : HalfDiagram N × HalfDiagram N //
  propagatingLabels N HK.1 = propagatingLabels N HK.2 }

def glue (H K : HalfDiagram N)
    (h : propagatingLabels N H = propagatingLabels N K) : Diagram N := ⟨(H,K),h⟩

-- An arc is (signed endpoint, positive paper label, signed endpoint).
abbrev Arc := ℤ × ℕ × ℤ

def hasArc (arcs : List Arc) (i : ℤ) (label : ℕ) (j : ℤ) : Bool :=
  arcs.any fun a => a.2.1 == label &&
    ((a.1 == i && a.2.2 == j) || (a.1 == j && a.2.2 == i))

def diagramArcs (D : Diagram N) : List Arc :=
  let H := D.val.1
  let K := D.val.2
  let left := (List.finRange N).filterMap fun i =>
    if i < H.val.1 i then some ((i.val+1:ℤ), (H.val.2 i).val+1, ((H.val.1 i).val+1:ℤ))
    else none
  let right := (List.finRange N).filterMap fun i =>
    if i < K.val.1 i then some (-((i.val+1:ℕ):ℤ), (K.val.2 i).val+1,
      -(((K.val.1 i).val+1:ℕ):ℤ)) else none
  let propagating := (List.finRange N).filterMap fun i =>
    if H.val.1 i = i then
      let j := ((List.finRange N).find? fun j =>
        K.val.1 j = j ∧ K.val.2 j = H.val.2 i).getD i
      some ((i.val+1:ℤ),(H.val.2 i).val+1,-((j.val+1:ℕ):ℤ))
    else none
  left ++ right ++ propagating

/- Constructive LexMin encoding from def:flat_diagram and
prop:right-code-factor (Okada.tex 4340–4379, 4569–4622).
Remove the top identity arc if present; otherwise flatten the largest right
descent arc and append N-1,...,d. No determinant or witness data enters it. -/
def flattenWord : ℕ → List Arc → List ℕ
  | 0, _ => []
  | n+1, arcs =>
    let top : ℤ := (n+1:ℕ)
    if hasArc arcs top (n+1) (-top) then
      flattenWord n (arcs.filter fun a => !hasArc [a] top (n+1) (-top))
    else
      let d : ℕ := ((List.range (n+1)).filter fun (d : ℕ) => 0 < d &&
        hasArc arcs (-(d:ℤ)) d (-((d+1:ℕ):ℤ))).foldl max 0
      let flat : ℤ → ℤ := fun t =>
        if t = top then -(n:ℤ)
        else if t < 0 ∧ d+2 ≤ t.natAbs then -((t.natAbs-2:ℕ):ℤ)
        else t
      flattenWord n ((arcs.filter fun a =>
        !hasArc [a] (-(d:ℤ)) d (-((d+1:ℕ):ℤ))).map fun a =>
          (flat a.1,a.2.1,flat a.2.2)) ++
        ((List.range n).reverse.map (fun i => i+1)).filter (fun i => d ≤ i)

def diagramElement (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) (D : Diagram N) :
    Presented N 𝕂 X Y :=
  ((flattenWord N (diagramArcs N D)).map fun i =>
    if h : 0 < i ∧ i < N then generator N 𝕂 X Y ⟨i-1,by omega⟩ else 0).prod

-- Coordinates in the diagram basis. The non-basis branch makes the
-- definition total; bijectivity is established at rank three below.
open scoped Classical in
def diagramCoefficient (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂)
    (D : Diagram N) (z : Presented N 𝕂 X Y) : 𝕂 :=
  if h : Function.Bijective (Fintype.linearCombination 𝕂 (diagramElement N 𝕂 X Y)) then
    (LinearEquiv.ofBijective (Fintype.linearCombination 𝕂 (diagramElement N 𝕂 X Y)) h).symm z D else 0

abbrev CellHalf (S : FibonacciSet N) :=
  { H : HalfDiagram N // propagatingLabels N H = S.val }

-- Coefficient realization of eq.cell-module-action in the diagram basis:
-- keep the output with the prescribed ket and propagating label set.
def cellAction (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂)
    (S : FibonacciSet N) (z : Presented N 𝕂 X Y) (v : CellHalf N S → 𝕂) :
    CellHalf N S → 𝕂 := fun H =>
  ∑ K, v K * diagramCoefficient N 𝕂 X Y
    (glue N H.val K.val (H.prop.trans K.prop.symm))
    (z * diagramElement N 𝕂 X Y (glue N K.val K.val rfl))

-- Definition 7.7: the scalar in E_(H ⋈ H) • K = c • H.
-- The zero branch totalizes the expression when this equation has no solution.
open scoped Classical in
def cellForm (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂)
    (S : FibonacciSet N) (H K : CellHalf N S) : 𝕂 :=
  if h : ∃ c : 𝕂, cellAction N 𝕂 X Y S
      (diagramElement N 𝕂 X Y (glue N H.val H.val rfl)) (Pi.single K 1) =
      c • Pi.single H 1 then Classical.choose h else 0

def cellGram (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂) (S : FibonacciSet N) :
    Matrix (CellHalf N S) (CellHalf N S) 𝕂 := cellForm N 𝕂 X Y S

def claim : Prop := ∀ (N : ℕ), 0 < N → ∀ (𝕂 : Type) [Field 𝕂]
  (X : Fin (N-1) → 𝕂) (Y : Fin (N-2) → 𝕂),
  Matrix.det (regularGram N 𝕂 X Y) =
    ∏ S : FibonacciSet N, (Matrix.det (cellGram N 𝕂 X Y S)) ^ (2 * Fintype.card (CellHalf N S))

private def halfTop : HalfDiagram 3 := ⟨(![0,1,2],![0,1,2]),by decide⟩
private def halfThree : HalfDiagram 3 := ⟨(![1,0,2],![0,0,2]),by decide⟩
private def halfOneB : HalfDiagram 3 := ⟨(![0,2,1],![0,1,1]),by decide⟩
private def halfOneA : HalfDiagram 3 := ⟨(![1,0,2],![0,0,0]),by decide⟩

private def rank3Diagrams : Fin 6 → Diagram 3 := ![
  glue 3 halfTop halfTop rfl,
  glue 3 halfThree halfThree rfl,
  glue 3 halfOneB halfOneB rfl,
  glue 3 halfOneA halfOneB (by decide),
  glue 3 halfOneB halfOneA (by decide),
  glue 3 halfOneA halfOneA rfl]

private def permTable : Fin 6 → Equiv.Perm (Fin 3) := ![
  1,Equiv.swap 0 1,Equiv.swap 1 2,
  Equiv.swap 0 1 * Equiv.swap 1 2,
  Equiv.swap 1 2 * Equiv.swap 0 1,
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1]

-- The diagrams and permutations are reindexed together in precisely the six
-- LexMin words [],[1],[2],[1,2],[2,1],[1,2,1].
private def permSix : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective permTable (by decide)

private def diagramSix : Fin 6 ≃ Diagram 3 :=
  Equiv.ofBijective rank3Diagrams (by decide +kernel)

private def fiboTop : FibonacciSet 3 := ⟨{0,1,2},by decide⟩
private def fiboThree : FibonacciSet 3 := ⟨{2},by decide⟩
private def fiboOne : FibonacciSet 3 := ⟨{0},by decide⟩

private def fiboTable : Fin 3 → FibonacciSet 3 := ![fiboTop,fiboThree,fiboOne]
private def fiboThreeEquiv : Fin 3 ≃ FibonacciSet 3 :=
  Equiv.ofBijective fiboTable (by decide +kernel)

private def cellTopTable : Fin 1 → CellHalf 3 fiboTop := ![⟨halfTop,by decide⟩]
private def cellThreeTable : Fin 1 → CellHalf 3 fiboThree := ![⟨halfThree,by decide⟩]
private def cellOneTable : Fin 2 → CellHalf 3 fiboOne := ![
  ⟨halfOneB,by decide⟩,⟨halfOneA,by decide⟩]

private def cellTopEquiv : Fin 1 ≃ CellHalf 3 fiboTop :=
  Equiv.ofBijective cellTopTable (by decide +kernel)
private def cellThreeEquiv : Fin 1 ≃ CellHalf 3 fiboThree :=
  Equiv.ofBijective cellThreeTable (by decide +kernel)
private def cellOneEquiv : Fin 2 ≃ CellHalf 3 fiboOne :=
  Equiv.ofBijective cellOneTable (by decide +kernel)

theorem result : ¬ claim := by
  classical
  obtain ⟨B,hB⟩ := rank3_basis_exists
  have ha : modelHom a = modelA := by
    unfold modelHom a generator
    rw [RingQuot.liftAlgHom_mkAlgHom_apply]
    simp
  have hb : modelHom b = modelB := by
    unfold modelHom b generator
    rw [RingQuot.liftAlgHom_mkAlgHom_apply]
    simp
  have hw : ∀ i, modelHom (sixWords i) = modelWords i := by
    intro i
    fin_cases i <;> simp [sixWords,modelWords,ha,hb]
  have hlin : B.equivFun.toLinearMap =
      modelCoordinates.toLinearMap.comp modelHom.toLinearMap := by
    apply B.ext
    intro i
    ext j
    simp only [LinearEquiv.coe_coe,LinearMap.coe_comp,AlgHom.coe_toLinearMap,
      Function.comp_apply,←hB i,Basis.equivFun_self]
    rw [hB,hw]
    fin_cases i <;> fin_cases j <;>
      norm_num [modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ,
        Matrix.one_apply]
  have hc : ∀ z i, B.repr z i = modelCoordinates (modelHom z) i := by
    intro z i
    exact congrFun (LinearMap.congr_fun hlin z) i
  have hmodelBijective : Function.Bijective modelHom := by
    apply Function.Bijective.of_comp_left (f := modelCoordinates)
      (g := modelHom) _ modelCoordinates.injective
    change Function.Bijective (modelCoordinates.toLinearMap.comp modelHom.toLinearMap)
    rw [←hlin]
    exact B.equivFun.bijective
  let modelIso : Q3 ≃ₐ[ℚ] Model := AlgEquiv.ofBijective modelHom hmodelBijective
  have ht : ∀ z : Q3, LinearMap.trace ℚ Q3 (Algebra.lmul ℚ Q3 z) =
      ∑ i : Fin 6, modelCoordinates (modelHom (z*sixWords i)) i := by
    intro z
    rw [LinearMap.trace_eq_matrix_trace ℚ B]
    simp only [Matrix.trace,Matrix.diag,Algebra.toMatrix_lmul',hB,hc]
  have hlists : ∀ i : Fin 6, lexmin 3 (permSix i) =
      (![[],[0],[1],[0,1],[1,0],[0,1,0]] : Fin 6 → List (Fin 2)) i := by
    decide
  have hp : ∀ i, lexElement 3 ℚ witnessX witnessY (permSix i) = sixWords i := by
    intro i
    simp only [lexElement,hlists]
    fin_cases i <;> simp [sixWords,a,b,mul_assoc]
  let numericGram : Matrix (Fin 6) (Fin 6) ℚ :=
    !![6,3,4,2,2,2;3,3,2,2,2,2;4,2,8,4,4,2;
       2,2,4,2,4,2;2,2,4,4,2,2;2,2,2,2,2,2]
  have hg : (regularGram 3 ℚ witnessX witnessY).submatrix permSix permSix = numericGram := by
    ext i j
    simp only [Matrix.submatrix_apply,regularGram,hp]
    rw [←map_mul (Algebra.lmul ℚ Q3),ht]
    simp only [map_mul,hw]
    fin_cases i <;> fin_cases j <;>
      norm_num [numericGram,modelCoordinates,modelWords,modelA,modelB,
        Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]
  have hd : numericGram.det = -16 := by
    let L : Matrix (Fin 6) (Fin 6) ℚ :=
      !![1,0,0,0,0,0;1/2,1,0,0,0,0;2/3,0,1,0,0,0;
         1/3,2/3,1/2,1,0,0;1/3,2/3,1/2,-2,1,0;1/3,2/3,1/8,-1/2,1/2,1]
    let U : Matrix (Fin 6) (Fin 6) ℚ :=
      !![6,3,4,2,2,2;0,3/2,0,1,1,1;0,0,16/3,8/3,8/3,2/3;
         0,0,0,-2/3,4/3,1/3;0,0,0,0,2,1;0,0,0,0,0,1/4]
    have hLU : L * U = numericGram := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [L,U,numericGram,Matrix.mul_apply,Fin.sum_univ_succ]
    have hL : L.IsLowerTriangular := by
      intro i j h
      change i.val < j.val at h
      fin_cases i <;> fin_cases j <;> (norm_num at h) <;> norm_num [L]
    have hU : U.IsUpperTriangular := by
      intro i j h
      fin_cases i <;> fin_cases j <;> (norm_num [Fin.lt_def] at h) <;> norm_num [U]
    have hLdiag : ∀ i, L i i = 1 := by
      intro i
      fin_cases i <;> norm_num [L]
    rw [←hLU,Matrix.det_mul,Matrix.det_of_isLowerTriangular L hL,
      Matrix.det_of_isUpperTriangular hU]
    simp only [hLdiag,Finset.prod_const_one,one_mul]
    norm_num [U,Fin.prod_univ_succ]
  have hregular : (regularGram 3 ℚ witnessX witnessY).det = -16 := by
    rw [←Matrix.det_reindex_self permSix.symm]
    change ((regularGram 3 ℚ witnessX witnessY).submatrix permSix permSix).det = -16
    rw [hg,hd]
  have hflat : ∀ i : Fin 6, flattenWord 3 (diagramArcs 3 (rank3Diagrams i)) =
      (![[],[1],[2],[1,2],[2,1],[1,2,1]] : Fin 6 → List ℕ) i := by
    decide +kernel
  have helem : ∀ i, diagramElement 3 ℚ witnessX witnessY (rank3Diagrams i) = sixWords i := by
    intro i
    simp only [diagramElement,hflat]
    fin_cases i <;> norm_num [sixWords,a,b,mul_assoc]
  let BD : Basis (Diagram 3) ℚ Q3 := B.reindex diagramSix
  have hBD : ∀ D, BD D = diagramElement 3 ℚ witnessX witnessY D := by
    intro D
    obtain ⟨i,rfl⟩ := diagramSix.surjective D
    rw [Basis.reindex_apply,Equiv.symm_apply_apply,hB]
    exact (helem i).symm
  have hexp : Fintype.linearCombination ℚ (diagramElement 3 ℚ witnessX witnessY) = BD.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro c
    change (∑ D, c D • diagramElement 3 ℚ witnessX witnessY D) = BD.equivFun.symm c
    rw [Basis.equivFun_symm_apply]
    simp only [hBD]
  have hbij : Function.Bijective (Fintype.linearCombination ℚ (diagramElement 3 ℚ witnessX witnessY)) := by
    rw [hexp]
    exact BD.equivFun.symm.bijective
  have hcoef : ∀ D z, diagramCoefficient 3 ℚ witnessX witnessY D z = BD.equivFun z D := by
    intro D z
    unfold diagramCoefficient
    rw [dif_pos hbij]
    have heq : LinearEquiv.ofBijective (Fintype.linearCombination ℚ (diagramElement 3 ℚ witnessX witnessY)) hbij =
        BD.equivFun.symm := by
      apply LinearEquiv.ext
      intro c
      exact LinearMap.congr_fun hexp c
    rw [heq]
    rfl
  have hco : ∀ i z, diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams i) z =
      modelCoordinates (modelHom z) i := by
    intro i z
    rw [hcoef]
    change (B.reindex diagramSix).repr z (diagramSix i) = _
    rw [Basis.repr_reindex_apply,Equiv.symm_apply_apply,hc]
  let gi : Matrix (Fin 2) (Fin 2) (Fin 6) := !![2,4;3,5]
  have hglueOne : ∀ i j : Fin 2,
      glue 3 (cellOneEquiv i).val (cellOneEquiv j).val
        ((cellOneEquiv i).prop.trans (cellOneEquiv j).prop.symm) = rank3Diagrams (gi i j) := by
    decide +kernel
  have source_coefficient_independence : ∀ (S : FibonacciSet 3)
      (F H K : CellHalf 3 S) (z : Q3),
      diagramCoefficient 3 ℚ witnessX witnessY
        (glue 3 F.val K.val (F.prop.trans K.prop.symm))
        (z * diagramElement 3 ℚ witnessX witnessY (glue 3 H.val K.val
          (H.prop.trans K.prop.symm))) =
      cellAction 3 ℚ witnessX witnessY S z (Pi.single H 1) F := by
    intro S
    obtain ⟨s,rfl⟩ := fiboThreeEquiv.surjective S
    fin_cases s
    · intro F H K z
      obtain ⟨i,rfl⟩ := cellTopEquiv.surjective F
      obtain ⟨j,rfl⟩ := cellTopEquiv.surjective H
      obtain ⟨k,rfl⟩ := cellTopEquiv.surjective K
      fin_cases i
      fin_cases j
      fin_cases k
      simp [cellAction,Pi.single_apply]
    · intro F H K z
      obtain ⟨i,rfl⟩ := cellThreeEquiv.surjective F
      obtain ⟨j,rfl⟩ := cellThreeEquiv.surjective H
      obtain ⟨k,rfl⟩ := cellThreeEquiv.surjective K
      fin_cases i
      fin_cases j
      fin_cases k
      simp [cellAction,Pi.single_apply]
    · intro F H K z
      obtain ⟨i,rfl⟩ := cellOneEquiv.surjective F
      obtain ⟨j,rfl⟩ := cellOneEquiv.surjective H
      obtain ⟨k,rfl⟩ := cellOneEquiv.surjective K
      simp [cellAction,Pi.single_apply]
      simp only [hglueOne,hco,helem,map_mul,hw]
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [gi,modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ] <;>
        ring
  have source_form_equation : ∀ (S : FibonacciSet 3) (H K : CellHalf 3 S),
      cellAction 3 ℚ witnessX witnessY S
        (diagramElement 3 ℚ witnessX witnessY (glue 3 H.val H.val rfl)) (Pi.single K 1) =
      (diagramCoefficient 3 ℚ witnessX witnessY
        (glue 3 H.val K.val (H.prop.trans K.prop.symm))
        (diagramElement 3 ℚ witnessX witnessY (glue 3 H.val H.val rfl) *
          diagramElement 3 ℚ witnessX witnessY (glue 3 K.val K.val rfl))) • Pi.single H 1 := by
    intro S
    obtain ⟨s,rfl⟩ := fiboThreeEquiv.surjective S
    fin_cases s
    · intro H K
      obtain ⟨i,rfl⟩ := cellTopEquiv.surjective H
      obtain ⟨j,rfl⟩ := cellTopEquiv.surjective K
      funext F
      obtain ⟨k,rfl⟩ := cellTopEquiv.surjective F
      fin_cases i
      fin_cases j
      fin_cases k
      simp [cellAction,Pi.single_apply]
    · intro H K
      obtain ⟨i,rfl⟩ := cellThreeEquiv.surjective H
      obtain ⟨j,rfl⟩ := cellThreeEquiv.surjective K
      funext F
      obtain ⟨k,rfl⟩ := cellThreeEquiv.surjective F
      fin_cases i
      fin_cases j
      fin_cases k
      simp [cellAction,Pi.single_apply]
    · intro H K
      obtain ⟨i,rfl⟩ := cellOneEquiv.surjective H
      obtain ⟨j,rfl⟩ := cellOneEquiv.surjective K
      funext F
      obtain ⟨k,rfl⟩ := cellOneEquiv.surjective F
      simp [cellAction,Pi.single_apply]
      simp only [hglueOne,hco,helem,map_mul,hw]
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [gi,modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ,
          ] <;> (intro h; have hn := cellOneEquiv.injective h; norm_num at hn)
  have hform : ∀ (S : FibonacciSet 3) (H K : CellHalf 3 S),
      cellForm 3 ℚ witnessX witnessY S H K =
      diagramCoefficient 3 ℚ witnessX witnessY
        (glue 3 H.val K.val (H.prop.trans K.prop.symm))
        (diagramElement 3 ℚ witnessX witnessY (glue 3 H.val H.val rfl) *
          diagramElement 3 ℚ witnessX witnessY (glue 3 K.val K.val rfl)) := by
    intro S H K
    have hex : ∃ c : ℚ, cellAction 3 ℚ witnessX witnessY S
        (diagramElement 3 ℚ witnessX witnessY (glue 3 H.val H.val rfl)) (Pi.single K 1) =
        c • Pi.single H 1 := ⟨_, source_form_equation S H K⟩
    unfold cellForm
    rw [dif_pos hex]
    have hs := congrFun (Classical.choose_spec hex) H
    have hi := source_coefficient_independence S H K K
      (diagramElement 3 ℚ witnessX witnessY (glue 3 H.val H.val rfl))
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hs
    exact hs.symm.trans hi.symm
  have hgtop : (cellGram 3 ℚ witnessX witnessY fiboTop).submatrix cellTopEquiv cellTopEquiv =
      (!![1] : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    change cellForm 3 ℚ witnessX witnessY _ _ _ = _
    rw [hform]
    fin_cases i
    fin_cases j
    change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 0)
      (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 0) *
        diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 0)) = 1
    simp only [hco,helem,map_mul,hw]
    norm_num [modelCoordinates,modelWords,Matrix.one_apply]
  have hgthree : (cellGram 3 ℚ witnessX witnessY fiboThree).submatrix cellThreeEquiv cellThreeEquiv =
      (!![1] : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    change cellForm 3 ℚ witnessX witnessY _ _ _ = _
    rw [hform]
    fin_cases i
    fin_cases j
    change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 1)
      (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 1) *
        diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 1)) = 1
    simp only [hco,helem,map_mul,hw]
    norm_num [modelCoordinates,modelWords,modelA,Matrix.mul_apply,Fin.sum_univ_succ]
  have hgone : (cellGram 3 ℚ witnessX witnessY fiboOne).submatrix cellOneEquiv cellOneEquiv =
      (!![2,1;1,1] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    change cellForm 3 ℚ witnessX witnessY _ _ _ = _
    rw [hform]
    fin_cases i <;> fin_cases j
    · change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 2)
        (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 2) *
          diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 2)) = 2
      simp only [hco,helem,map_mul,hw]
      norm_num [modelCoordinates,modelWords,modelB,Matrix.mul_apply,Fin.sum_univ_succ,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail]
    · change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 4)
        (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 2) *
          diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 5)) = 1
      simp only [hco,helem,map_mul,hw]
      norm_num [modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
        Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail]
    · change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 3)
        (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 5) *
          diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 2)) = 1
      simp only [hco,helem,map_mul,hw]
      norm_num [modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
        Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail]
    · change diagramCoefficient 3 ℚ witnessX witnessY (rank3Diagrams 5)
        (diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 5) *
          diagramElement 3 ℚ witnessX witnessY (rank3Diagrams 5)) = 1
      simp only [hco,helem,map_mul,hw]
      norm_num [modelCoordinates,modelWords,modelA,modelB,Matrix.mul_apply,Fin.sum_univ_succ,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail] <;> rfl
  have hdetTop : (cellGram 3 ℚ witnessX witnessY fiboTop).det = 1 := by
    rw [←Matrix.det_reindex_self cellTopEquiv.symm]
    change ((cellGram 3 ℚ witnessX witnessY fiboTop).submatrix cellTopEquiv cellTopEquiv).det = 1
    rw [hgtop]
    norm_num [Matrix.det_unique]
  have hdetThree : (cellGram 3 ℚ witnessX witnessY fiboThree).det = 1 := by
    rw [←Matrix.det_reindex_self cellThreeEquiv.symm]
    change ((cellGram 3 ℚ witnessX witnessY fiboThree).submatrix cellThreeEquiv cellThreeEquiv).det = 1
    rw [hgthree]
    norm_num [Matrix.det_unique]
  have hdetOne : (cellGram 3 ℚ witnessX witnessY fiboOne).det = 1 := by
    rw [←Matrix.det_reindex_self cellOneEquiv.symm]
    change ((cellGram 3 ℚ witnessX witnessY fiboOne).submatrix cellOneEquiv cellOneEquiv).det = 1
    rw [hgone]
    norm_num [Matrix.det_fin_two]
  have hdimTop : Fintype.card (CellHalf 3 fiboTop) = 1 := by
    simpa using Fintype.card_congr cellTopEquiv.symm
  have hdimThree : Fintype.card (CellHalf 3 fiboThree) = 1 := by
    simpa using Fintype.card_congr cellThreeEquiv.symm
  have hdimOne : Fintype.card (CellHalf 3 fiboOne) = 2 := by
    simpa using Fintype.card_congr cellOneEquiv.symm
  have hall : ∀ S : FibonacciSet 3, (cellGram 3 ℚ witnessX witnessY S).det = 1 := by
    intro S
    obtain ⟨i,rfl⟩ := fiboThreeEquiv.surjective S
    fin_cases i
    · exact hdetTop
    · exact hdetThree
    · exact hdetOne
  have hrhs : (∏ S : FibonacciSet 3,
      (cellGram 3 ℚ witnessX witnessY S).det ^ (2 * Fintype.card (CellHalf 3 S))) = 1 := by
    simp only [hall,one_pow,Finset.prod_const_one]
  intro hclaim
  have h := @hclaim 3 (by decide) ℚ inferInstance witnessX witnessY
  rw [hregular,hrhs] at h
  norm_num at h


end
end D5.S0.Certificates.Combinatorics.OkadaDiscriminantRefutation
