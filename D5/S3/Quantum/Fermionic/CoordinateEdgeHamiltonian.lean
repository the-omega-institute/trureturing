/- GID: D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian
   mirror-E: none(waiver:general-quadratic-interactions)
   anchors: [mathlib/module/Mathlib.Analysis.CStarAlgebra.CStarMatrix]
   utility: none
   digest: Real conference coefficients realize normalized quadratic coordinate interactions. -/

/-
coordinate_edges_admissible:
  proof_shape: content
  escape_witness: coordinate_edges_admissible (form 2): identify the sole changed
    coordinate and construct its real coefficient on each actual unordered graph edge.
admission_basis: escape-witness
Same-delivery inlined content: FockMajoranaCarrier, CompleteCartesianGraph, ConferenceMatrices, and local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  GID: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant.occupationCount
    statement_id: sha256:97804cfc85a668f345a5b3e2421ba02e5e6203f36590508faccac8726341bc0a
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.FullOperator
    statement_id: sha256:d0e241c65c207456599a205d965adefde23f6764456a0c5a832a08a676fadfb3
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.Local
    statement_id: sha256:cea3034ad5d4c2d36ac899cc7964a23cdad5b9a52b0410ee01f4b03ffd41f349
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fermionWord
    statement_id: sha256:d1484b5db3ace7148c685690abf5667976f26043e824bad34ea4385d5015100d
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC
    statement_id: sha256:e5eb14acc0a2901b62190a83ed2543f27309f7f32708edd35fa0376362ebfe97
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_CAR
    statement_id: sha256:91a39cca0cc0155aec0a40a8280d10bd356a0d091f81f8031b64299b1ade63de
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_anticomm_of_lt
    statement_id: sha256:1db13273a320d9215f5583b5d1bcd5cf5cff7952171e37a663fc509057aaacd4
  GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner.fullC_mixed_anticomm_of_lt
    statement_id: sha256:eb93c9ae1da812ac8631c45850a4bd5f0d160da82cbfe9ad9d4377f14362f664
  GID: D5/S3/Quantum/Dynamics/ClauseHamiltonian.Assignment
    statement_id: sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
computational_content.kind: none; arbitrary site counts, mode counts and conference orders.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.Fermionic.CompleteCartesianGraph
import D5.S3.Quantum.Fermionic.ConferenceMatrices

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder CStarAlgebra
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
open D5.S3.Quantum.Fermionic.CompleteCartesianGraph
open D5.S3.Quantum.Fermionic.ConferenceMatrices

noncomputable section
namespace D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian

def quadraticEdge {n m : ℕ} (v w : Fin n)
    (K : Matrix (Fin m × Bool) (Fin m × Bool) ℝ) :
    CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ :=
  CStarMatrix.ofMatrix (Complex.I • ∑ p : Fin m × Bool, ∑ q : Fin m × Bool,
    (K p q : ℂ) • (majorana (finProdFinEquiv (v,p.1)) p.2 *
      majorana (finProdFinEquiv (w,q.1)) q.2))

open Classical in
def averagedHamiltonian {n m : ℕ} (G : SimpleGraph (Fin n))
    (K : G.edgeSet → Matrix (Fin m × Bool) (Fin m × Bool) ℝ) :
    CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ :=
  (G.edgeFinset.card : ℝ)⁻¹ • ∑ e : G.edgeSet, quadraticEdge e.val.out.1 e.val.out.2 (K e)

open Classical in
def admissibleEdges {n m : ℕ} (G : SimpleGraph (Fin n))
    (K : G.edgeSet → Matrix (Fin m × Bool) (Fin m × Bool) ℝ) : Prop :=
  ∀ e : G.edgeSet,
    IsSelfAdjoint (quadraticEdge e.val.out.1 e.val.out.2 (K e)) ∧
    ‖quadraticEdge e.val.out.1 e.val.out.2 (K e)‖ ≤ 1 ∧
    Commute (quadraticEdge e.val.out.1 e.val.out.2 (K e))
      (CStarMatrix.ofMatrix (numberParity (n*m)))

open Classical in
/-- Real diagonal Majorana coupling on an actual coordinate edge, with its chosen orientation. -/
def coordinateCoupling {n q m : ℕ} (r : ℕ) (e : Fin n ≃ (Fin q → Index r))
    (a : Fin q ≃ Fin m × Bool)
    (z : ((coordinateGraph q (Index r)).comap e).edgeSet) :
    Matrix (Fin m × Bool) (Fin m × Bool) ℝ := fun p u =>
  if p = u ∧ ∀ b, b ≠ a.symm p → e z.val.out.1 b = e z.val.out.2 b
  then (conference r (e z.val.out.1 (a.symm p)) (e z.val.out.2 (a.symm p)) : ℝ)
  else 0

open Classical in
/-- Each actual edge has one real sign coefficient and gives an admissible quadratic interaction. -/
theorem coordinate_edges_admissible {n q m : ℕ} (r : ℕ)
    (e : Fin n ≃ (Fin q → Index r)) (a : Fin q ≃ Fin m × Bool) :
    admissibleEdges ((coordinateGraph q (Index r)).comap e) (coordinateCoupling r e a) ∧
    ∀ z : ((coordinateGraph q (Index r)).comap e).edgeSet,
      ∃ t : Fin q, e z.val.out.1 t ≠ e z.val.out.2 t ∧
        coordinateCoupling r e a z =
          Matrix.single (a t) (a t) (conference r (e z.val.out.1 t) (e z.val.out.2 t) : ℝ) := by
  classical
  have hcontract {n m : ℕ} (v w : Fin n) (hvw : v ≠ w) (p : Fin m × Bool)
      (z : ℝ) (hz : z = 1 ∨ z = -1) :
      IsSelfAdjoint (quadraticEdge v w (Matrix.single p p z)) ∧
      ‖quadraticEdge v w (Matrix.single p p z)‖ ≤ 1 ∧
      Commute (quadraticEdge v w (Matrix.single p p z))
        (CStarMatrix.ofMatrix (numberParity (n*m))) := by
    classical
    let A := majorana (finProdFinEquiv (v,p.1)) p.2
    let B := majorana (finProdFinEquiv (w,p.1)) p.2
    have hab : (finProdFinEquiv (v,p.1),p.2) ≠ (finProdFinEquiv (w,p.1),p.2) := by
      intro h
      exact hvw (congrArg Prod.fst (finProdFinEquiv.injective (congrArg Prod.fst h)))
    have hc := majorana_clifford_and_parity (n*m)
    have hA : A.IsHermitian := hc.2.2.1 (finProdFinEquiv (v,p.1),p.2)
    have hB : B.IsHermitian := hc.2.2.1 (finProdFinEquiv (w,p.1),p.2)
    have hsA : A*A = 1 := by
      have h := hc.2.2.2.1 (finProdFinEquiv (v,p.1),p.2) (finProdFinEquiv (v,p.1),p.2)
      simp only [ite_true, two_smul] at h
      change A*A + A*A = 1+1 at h
      ext s t
      have hh := congrArg (fun M : FullOperator (n*m) => M s t) h
      simp only [Matrix.add_apply] at hh
      linear_combination (1/2 : ℂ) * hh
    have hsB : B*B = 1 := by
      have h := hc.2.2.2.1 (finProdFinEquiv (w,p.1),p.2) (finProdFinEquiv (w,p.1),p.2)
      simp only [ite_true, two_smul] at h
      change B*B + B*B = 1+1 at h
      ext s t
      have hh := congrArg (fun M : FullOperator (n*m) => M s t) h
      simp only [Matrix.add_apply] at hh
      linear_combination (1/2 : ℂ) * hh
    have hAB : A*B = -(B*A) := by
      have h := hc.2.2.2.1 (finProdFinEquiv (v,p.1),p.2) (finProdFinEquiv (w,p.1),p.2)
      rw [if_neg hab] at h
      change A*B + B*A = 0 at h
      exact eq_neg_of_add_eq_zero_left h
    have he : quadraticEdge v w (Matrix.single p p z) =
        CStarMatrix.ofMatrix ((Complex.I * (z : ℂ)) • (A*B)) := by
      simp [quadraticEdge, Matrix.single_apply, ite_and, eq_comm, A, B]
      ext s t
      simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      ring
    have hzsq : (z : ℂ)*(z : ℂ) = 1 := by rcases hz with rfl | rfl <;> norm_num
    have hHerm : ((Complex.I * (z : ℂ)) • (A*B)).IsHermitian := by
      rw [Matrix.IsHermitian]
      simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hA.eq, hB.eq,
        star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      rw [show (z : ℂ) * -Complex.I = -(Complex.I * (z : ℂ)) by ring,
        neg_smul, show B*A = -(A*B) by rw [hAB, neg_neg], smul_neg, neg_neg]
    have hs : ((Complex.I * (z : ℂ)) • (A*B)) *
        ((Complex.I * (z : ℂ)) • (A*B)) = 1 := by
      have hh : A*B*(A*B) = -1 := by
        calc
          _ = A*(B*A)*B := by noncomm_ring
          _ = -(A*(A*B)*B) := by rw [show B*A = -(A*B) by rw [hAB, neg_neg]]; simp
          _ = -1 := by simp [← Matrix.mul_assoc, hsA, hsB]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]
      have hi : (Complex.I*(z : ℂ))*(Complex.I*(z : ℂ)) = -1 := by
        calc
          _ = (Complex.I*Complex.I)*((z : ℂ)*(z : ℂ)) := by ring
          _ = -1 := by rw [Complex.I_mul_I, hzsq, mul_one]
      rw [hi]
      simp
    have hself : IsSelfAdjoint (quadraticEdge v w (Matrix.single p p z)) := by
      rw [he]
      exact hHerm.isSelfAdjoint.map CStarMatrix.ofMatrixStarAlgEquiv
    refine ⟨hself, ?_, ?_⟩
    · have hu : quadraticEdge v w (Matrix.single p p z) ∈
          unitary (CStarMatrix (Assignment (n*m)) (Assignment (n*m)) ℂ) := by
        rw [Unitary.mem_iff, hself.star_eq]
        have hsq : quadraticEdge v w (Matrix.single p p z) *
            quadraticEdge v w (Matrix.single p p z) = 1 := by
          rw [he]
          exact congrArg CStarMatrix.ofMatrix hs
        exact ⟨hsq,hsq⟩
      exact (CStarRing.norm_of_mem_unitary hu).le
    · rw [he, commute_iff_eq]
      change ((Complex.I*(z : ℂ)) • (A*B))*numberParity (n*m) =
        numberParity (n*m)*((Complex.I*(z : ℂ)) • (A*B))
      rw [Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      have hpA : numberParity (n*m)*A = -(A*numberParity (n*m)) := eq_neg_of_add_eq_zero_left (hc.2.2.2.2 (finProdFinEquiv (v,p.1),p.2))
      have hpB : numberParity (n*m)*B = -(B*numberParity (n*m)) := eq_neg_of_add_eq_zero_left (hc.2.2.2.2 (finProdFinEquiv (w,p.1),p.2))
      symm
      rw [← Matrix.mul_assoc, hpA, Matrix.neg_mul, Matrix.mul_assoc, hpB,
        Matrix.mul_neg, neg_neg]
      simp only [Matrix.mul_assoc]
  have hcoeff (z : ((coordinateGraph q (Index r)).comap e).edgeSet) :
    ∃ t : Fin q,
      e z.val.out.1 t ≠ e z.val.out.2 t ∧
      coordinateCoupling r e a z =
      Matrix.single (a t) (a t) (conference r (e z.val.out.1 t) (e z.val.out.2 t) : ℝ) := by
    have hadj : ((coordinateGraph q (Index r)).comap e).Adj z.val.out.1 z.val.out.2 := by
      have h := z.property
      rw [← z.val.out_eq] at h
      exact h
    change (∃ t, e z.val.out.1 t ≠ e z.val.out.2 t ∧
      ∀ b, b ≠ t → e z.val.out.1 b = e z.val.out.2 b) at hadj
    obtain ⟨t,ht,hrest⟩ := hadj
    refine ⟨t,ht,?_⟩
    unfold coordinateCoupling
    ext p u
    by_cases hpu : p = u
    · subst u
      by_cases hpt : p = a t
      · subst p
        simp only [Equiv.symm_apply_apply]
        rw [if_pos ⟨True.intro, hrest⟩]
        simp [Matrix.single_apply]
      · have hat : a.symm p ≠ t := by
          intro h
          exact hpt (by rw [← h, a.apply_symm_apply])
        have hx := hrest (a.symm p) hat
        simp [Matrix.single_apply, Ne.symm hpt, hx, (conference_properties r).2.2.1]
    · simp only [hpu, false_and, ite_false, Matrix.single_apply]
      split_ifs with h
      · exact False.elim (hpu (h.1.symm.trans h.2))
      · rfl
  refine ⟨?_, hcoeff⟩
  intro z
  obtain ⟨t,ht,heq⟩ := hcoeff z
  rw [heq]
  have hvw : z.val.out.1 ≠ z.val.out.2 := fun h => ht (congrArg (fun v => e v t) h)
  have hsign : (conference r (e z.val.out.1 t) (e z.val.out.2 t) : ℝ) = 1 ∨
      (conference r (e z.val.out.1 t) (e z.val.out.2 t) : ℝ) = -1 := by
    rcases (conference_properties r).2.2.2.1 _ _ ht with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  exact hcontract _ _ hvw (a t) _ hsign

end D5.S3.Quantum.Fermionic.CoordinateEdgeHamiltonian
