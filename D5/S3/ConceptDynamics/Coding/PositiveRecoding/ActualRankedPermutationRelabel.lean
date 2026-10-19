/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualRankedPermutationRelabel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ranked permutation factors as actual graph relabelings. -/

/- The permutation half-edge is unique. Arbitrary complementary fibers may be empty; every product edge uses the existing ranked split/join. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualRelabelParallelPhase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualRelabelResidue
open scoped BigOperators
open D5.S3.ConceptDynamics.Coding
open CountedMatrixOverlap
open CountedOrderTypeGyration
open CountedRelativeGyrationTransport
open ZeroWindowRelabeling (Relabel)

def P {n m : ℕ} (e : Fin n ≃ Fin m) : CountMat n m :=
  fun i j => if e i = j then 1 else 0

def Q {n m : ℕ} (e : Fin n ≃ Fin m) (A : CountMat n n) : CountMat m n :=
  fun j i => A (e.symm j) i

theorem P_mul_Q {n m : ℕ} (e : Fin n ≃ Fin m) (A : CountMat n n) :
    P e * Q e A = A := by
  classical
  ext i k
  simp [Matrix.mul_apply, P, Q, ite_mul]

theorem Q_mul_P {n m : ℕ} (e : Fin n ≃ Fin m) (A : CountMat n n) :
    Q e A * P e = fun j k => A (e.symm j) (e.symm k) := by
  classical
  ext j k
  change (∑ i, A (e.symm j) i * (if e i = k then 1 else 0)) = _
  calc
    _ = ∑ l : Fin m, A (e.symm j) (e.symm l) * (if l = k then 1 else 0) := by
      apply Fintype.sum_equiv e
      intro i
      rw [e.symm_apply_apply]
    _ = _ := by simp [mul_ite]

/-- The distinguished P edge at i exists without any Q-edge existence
assumption. In dimension zero this is a function out of the empty type. -/
def pEdge {n m : ℕ} (e : Fin n ≃ Fin m) (i : Fin n) : Edge (P e) :=
  ⟨i, e i, ⟨0, by simp [P]⟩⟩

theorem p_target {n m : ℕ} (e : Fin n ≃ Fin m) (a : Edge (P e)) :
    a.target = e a.source := by
  classical
  have h := a.number.isLt
  by_contra hn
  have he : e a.source ≠ a.target := Ne.symm hn
  simp only [P, if_neg he] at h
  exact Nat.not_lt_zero _ h

theorem p_unique {n m : ℕ} (e : Fin n ≃ Fin m) (a : Edge (P e)) :
    a = pEdge e a.source := by
  apply edge_eq_coordinates (a := a) (b := pEdge e a.source) rfl (p_target e a)
  have h := a.number.isLt
  have he := (p_target e a).symm
  simp only [P, if_pos he] at h
  change a.number.val = 0
  omega

/-- Shift the actual Q half-edge left and append the unique P edge at the
OLD target. This defines an edge map, before any path is considered. -/
def rankedForward {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n)
    (a : Edge (P e * q)) : Edge (q * P e) :=
  join q (P e) (split (P e) q a).2 (pEdge e a.target) (split_target _ _ a)

def rankedInverse {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n)
    (b : Edge (q * P e)) : Edge (P e * q) :=
  join (P e) q (pEdge e (e.symm b.source)) (split q (P e) b).1
    (e.apply_symm_apply b.source)

theorem ranked_left {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n)
    (a : Edge (P e * q)) : rankedInverse e q (rankedForward e q a) = a := by
  have hp : pEdge e (e.symm (split (P e) q a).2.source) =
      (split (P e) q a).1 := by
    have hm : (split (P e) q a).2.source = e a.source :=
      (p_target e (split (P e) q a).1)
    rw [hm, e.symm_apply_apply]
    exact (p_unique e (split (P e) q a).1).symm
  unfold rankedInverse rankedForward
  simp only [split_join]
  change join (P e) q (pEdge e (e.symm (split (P e) q a).2.source))
    (split (P e) q a).2 _ = a
  simp only [hp]
  exact join_split (P e) q a

theorem ranked_right {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n)
    (b : Edge (q * P e)) : rankedForward e q (rankedInverse e q b) = b := by
  have hp : pEdge e (split q (P e) b).1.target = (split q (P e) b).2 := by
    exact (p_unique e (split q (P e) b).2).symm
  unfold rankedForward rankedInverse
  simp only [split_join]
  change join q (P e) (split q (P e) b).1
    (pEdge e (split q (P e) b).1.target) _ = b
  simp only [hp]
  exact join_split q (P e) b

/-- The actual ranked elementary recoding is a graph relabel in this case.
Both inverses have just been proved using split/join, not cardinality. -/
def rankedRelabel {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n) :
    Relabel (countedGraph (P e * q)) (countedGraph (q * P e)) where
  vertex := e
  edge := ⟨rankedForward e q, rankedInverse e q, ranked_left e q, ranked_right e q⟩
  source a := p_target e (split (P e) q a).1
  target _ := rfl

theorem ranked_coordinate {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n)
    (x : Path (P e * q)) (t : ℤ) :
    (elementaryHomeomorph (P e) q x).val t = (rankedRelabel e q).edge (x.val t) := by
  rw [elementary_coordinate]
  have hp : (split (P e) q (x.val (t+1))).1 = pEdge e (x.val t).target := by
    rw [p_unique e (split (P e) q (x.val (t+1))).1]
    exact congrArg (pEdge e) (x.property t).symm
  change join q (P e) (split (P e) q (x.val t)).2
    (split (P e) q (x.val (t+1))).1 (x.property t) =
    join q (P e) (split (P e) q (x.val t)).2 (pEdge e (x.val t).target)
      (split_target (P e) q (x.val t))
  simp only [hp]

theorem ranked_timed {n m : ℕ} (e : Fin n ≃ Fin m) (q : CountMat m n) :
    timed (rankedRelabel e q) = TimedEquiv.elementary (P e) q := by
  apply TimedEquiv.ext
  intro x
  apply Subtype.ext
  funext t
  exact (ranked_coordinate e q x t).symm

theorem ranked_residue {n m d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (e : Fin n ≃ Fin m) (q : CountMat m n)
    {A : CountMat n n} {B : CountMat m m}
    (hA : P e * q = A) (hB : q * P e = B)
    (r : Relabel (countedGraph A) (countedGraph B)) (hv : r.vertex = e) :
    ZMod.castHom hd (ZMod 3) ((timed r).gyration d) =
      ZMod.castHom hd (ZMod 3) (relativeForwardGyration (d := d) (P e) q) := by
  subst A
  subst B
  calc
    _ = ZMod.castHom hd (ZMod 3) ((timed (rankedRelabel e q)).gyration d) :=
      same_vertex_residue hd r (rankedRelabel e q) hv
    _ = _ := by rw [ranked_timed, TimedEquiv.gyration_elementary]

end SourceOnly.ActualRelabelResidue
