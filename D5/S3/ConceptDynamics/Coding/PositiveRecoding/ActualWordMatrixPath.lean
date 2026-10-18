/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordMatrixPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite graph words give chronological rectangular RS paths and exact scalar-extended endpoint maps. -/
import D5.S3.ConceptDynamics.Coding.FiniteKernelLadder
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.ActualPositiveWordPeriodicCochain
import D5.S3.ConceptDynamics.Coding.BeamColimits.PositiveWordBeamTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SourceOnly.ActualWordMatrixPath

open D5.S3.ConceptDynamics.Coding
open EssentialWordRealization TwoSidedFiniteInduction TypedPositiveSplitWord
open ZeroWindowRelabeling (Relabel)
open CountedMatrixOverlap (CountMat)
open CountedOrderTypeGyration (GyrationDyadic dyadicGyration)
open SourceOnly.FiniteKernelLadder (Based Edge Path)
open SourceOnly.KernelRSSquareGyration (rows rows_comp)
open scoped BigOperators Matrix

abbrev D := GyrationDyadic

def counts {n m : ℕ} (A : CountMat n m) : Matrix (Fin n) (Fin m) D :=
  (A.map (Nat.castRingHom ℤ)).map (algebraMap ℤ D)

theorem counts_mul {n m p : ℕ} (R : CountMat n m) (S : CountMat m p) :
    counts (R*S) = counts R * counts S := by
  simp only [counts, Matrix.map_mul]

/-- This acts on column vectors of vertex coefficients. Its COLUMN matrix
is the transpose of A; its ROW matrix is A. -/
theorem rows_right {n m : ℕ} (A : Matrix (Fin n) (Fin m) D) :
    rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin m))
      A.toLinearMapRight' = A := by
  ext i j
  simp only [rows, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, Matrix.toLinearMapRight'_apply,
    Matrix.single_vecMul, Matrix.row, one_smul]

/-- A coefficient reindexing over the same dyadic ring as the cochain. -/
def reindex {V W : Type} (e : V ≃ W) : (V → D) ≃ₗ[D] (W → D) where
  toFun z w := z (e.symm w)
  invFun z v := z (e v)
  left_inv z := by funext v; exact congrArg z (e.symm_apply_apply v)
  right_inv z := by funext w; exact congrArg z (e.apply_symm_apply w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Graph
variable {V E W J : Type} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype J] [DecidableEq W]
  {G : DirectedMultigraph V E} {H : DirectedMultigraph W J}

/-- The existing integer adjacency counts actual outgoing edges. It is
extended coefficient by coefficient, without taking any kernel quotient. -/
def timeMap (G : DirectedMultigraph V E) : Module.End D (V → D) :=
  ((StandardBeamEndpointRows.adjacency G).map (algebraMap ℤ D)).toLinearMapRight'

def based (G : DirectedMultigraph V E) {n : ℕ}
    (b : Module.Basis (Fin n) D (V → D)) : Based where
  V := V → D
  dim := n
  basis := b
  time := timeMap G

/-- Exact coefficient equation obtained from the actual edge bijection,
not a postulated conjugacy of adjacency matrices. -/
theorem relabel_adjacency (r : Relabel G H) (v : V) (w : W) :
    StandardBeamEndpointRows.adjacency G v (r.vertex.symm w) =
      StandardBeamEndpointRows.adjacency H (r.vertex v) w := by
  exact congrFun (FiniteRelabelBeamTransport.reindex_adjacency r v) w

theorem relabel_time (r : Relabel G H) :
    (reindex r.vertex).toLinearMap.comp (timeMap G) =
      (timeMap H).comp (reindex r.vertex).toLinearMap := by
  classical
  apply LinearMap.ext
  intro z
  funext w
  change (∑ v : V, z v * algebraMap ℤ D
      (StandardBeamEndpointRows.adjacency G v (r.vertex.symm w))) =
    ∑ v : W, z (r.vertex.symm v) * algebraMap ℤ D
      (StandardBeamEndpointRows.adjacency H v w)
  apply Fintype.sum_equiv r.vertex
  intro v
  rw [r.vertex.symm_apply_apply, relabel_adjacency r v w]

/-- A relabel is an actual lag-one RS edge: r=e and s=T_G e^{-1}.
Only the vertex bijection is inverted; no time map is inverted. -/
def relabelEdge {n m : ℕ} (r : Relabel G H)
    (bG : Module.Basis (Fin n) D (V → D))
    (bH : Module.Basis (Fin m) D (W → D)) : Edge (based G bG) (based H bH) where
  r := (reindex r.vertex).toLinearMap
  s := (timeMap G).comp (reindex r.vertex).symm.toLinearMap
  sr := by
    apply LinearMap.ext
    intro z
    funext v
    change timeMap G ((reindex r.vertex).symm (reindex r.vertex z)) v = timeMap G z v
    rw [LinearEquiv.symm_apply_apply]
  rs := by
    apply LinearMap.ext
    intro z
    change reindex r.vertex (timeMap G ((reindex r.vertex).symm z)) = timeMap H z
    exact (LinearMap.congr_fun (relabel_time r) ((reindex r.vertex).symm z)).trans
      (congrArg (timeMap H) ((reindex r.vertex).apply_symm_apply z))

end Graph

def countedBased {n : ℕ} (A : CountMat n n) : Based :=
  based (CountedOrderTypeGyration.countedGraph A) (Pi.basisFun D (Fin n))

theorem time_counted {n : ℕ} (A : CountMat n n) :
    timeMap (CountedOrderTypeGyration.countedGraph A) = (counts A).toLinearMapRight' := by
  unfold timeMap
  change ((StandardBeamEndpointRows.adjacency
    (CountedMatrixBeamDiagram.countedGraph A)).map (algebraMap ℤ D)).toLinearMapRight' = _
  rw [CountedMatrixBeamDiagram.adjacency_counted]
  rfl

theorem counted_matrix {n : ℕ} (A : CountMat n n) :
    (countedBased A).matrix = counts A := by
  change rows (Pi.basisFun D (Fin n)) (Pi.basisFun D (Fin n))
    (timeMap (CountedOrderTypeGyration.countedGraph A)) = _
  rw [time_counted, rows_right]

/-- The original ranked R,S, in their original chronological direction. -/
def positiveEdge {n m : ℕ} (R : CountMat n m) (S : CountMat m n) :
    Edge (countedBased (R*S)) (countedBased (S*R)) where
  r := (counts R).toLinearMapRight'
  s := (counts S).toLinearMapRight'
  sr := by
    change (counts S).toLinearMapRight'.comp (counts R).toLinearMapRight' = timeMap _
    rw [← Matrix.toLinearMapRight'_mul, ← counts_mul, time_counted]
  rs := by
    change (counts R).toLinearMapRight'.comp (counts S).toLinearMapRight' = timeMap _
    rw [← Matrix.toLinearMapRight'_mul, ← counts_mul, time_counted]

/-- Use precisely P1's outOld chart, including its actual vertex numbering. -/
def presentationBasis (F : Presentation) :
    Module.Basis (Fin (Fintype.card F.V)) D (F.V → D) :=
  (Pi.basisFun D (Fin (Fintype.card F.V))).map
    (reindex (ActualPositiveWordPeriodicCochain.chart F).vertex)

def vertex (F : Presentation) : Based := based F.graph (presentationBasis F)

/-- The graph matrix in this basis is derived from the actual chart's edge
bijection. It is not assumed to equal the original signed COLUMN T. -/
theorem vertex_matrix (F : Presentation) :
    (vertex F).matrix = counts (ActualPositiveWordPeriodicCochain.matrix F) := by
  have ht := (relabel_time (ActualPositiveWordPeriodicCochain.chart F)).symm
  have h := SourceOnly.FiniteKernelLadder.rows_transport
    (Pi.basisFun D (Fin (Fintype.card F.V)))
    (Pi.basisFun D (Fin (Fintype.card F.V)))
    (reindex (ActualPositiveWordPeriodicCochain.chart F).vertex)
    (reindex (ActualPositiveWordPeriodicCochain.chart F).vertex)
    (timeMap (CountedOrderTypeGyration.countedGraph
      (ActualPositiveWordPeriodicCochain.matrix F))) (timeMap F.graph) ht
  change (vertex F).matrix = _ at h
  exact h.trans (counted_matrix (ActualPositiveWordPeriodicCochain.matrix F))


/-- Relabel leaves cost one RS edge; positive leaves cost three because both
actual chart arrows are retained. This length is not Word.letters. -/
def length : ∀ {F H : Presentation}, Word F H → ℕ
  | _, _, .relabel _ => 1
  | _, _, .positive _ _ _ _ => 3
  | _, _, .comp u v => length u + length v

def dictionary : ∀ {F H : Presentation} (w : Word F H),
    Path (vertex F) (vertex H) (length w)
  | _, _, .relabel r => .cons (relabelEdge r _ _) (.nil _)
  | _, _, .positive R S old next =>
      .cons (relabelEdge old.symm _ (Pi.basisFun D _))
        (.cons (positiveEdge R S)
          (.cons (relabelEdge next (Pi.basisFun D _) _) (.nil _)))
  | _, _, .comp u v => (dictionary u).append (dictionary v)

namespace Path
variable {X Y Z : Based} {n m : ℕ}

private theorem forward_mpr {k l : ℕ} (h : k = l)
    (e : Path X Y l = Path X Y k) (u : Path X Y k) :
    (e.mpr u).forward = u.forward := by
  subst l
  have he : e = rfl := Subsingleton.elim _ _
  cases he
  rfl

theorem append_forward (u : Path X Y n) (v : Path Y Z m) :
    (u.append v).forward = v.forward.comp u.forward := by
  induction u with
  | nil X =>
      simp only [SourceOnly.FiniteKernelLadder.Path.append]
      rw [forward_mpr (Nat.zero_add m).symm]
      exact (LinearMap.comp_id _).symm
  | @cons X Y W k e tail ih =>
      simp only [SourceOnly.FiniteKernelLadder.Path.append]
      rw [forward_mpr (k := (k+m)+1) (l := (k+1)+m) (by omega)]
      simpa only [SourceOnly.FiniteKernelLadder.Path.forward,
        LinearMap.comp_assoc] using congrArg (fun f => f.comp e.r) (ih v)

end Path

/-- Scalar extension of B.endpointMap, using its actual constructor order. -/
def endpointMap : ∀ {F H : Presentation}, Word F H → (F.V → D) →ₗ[D] (H.V → D)
  | _, _, .relabel r => (reindex r.vertex).toLinearMap
  | _, _, .positive R S old next =>
      (reindex next.vertex).toLinearMap.comp
        ((counts R).toLinearMapRight'.comp (reindex old.vertex).symm.toLinearMap)
  | _, _, .comp u v => (endpointMap v).comp (endpointMap u)

theorem dictionary_forward : ∀ {F H : Presentation} (w : Word F H),
    (dictionary w).forward = endpointMap w
  | _, _, .relabel r => by
      simp only [dictionary, SourceOnly.FiniteKernelLadder.Path.forward,
        relabelEdge, endpointMap, LinearMap.id_comp]
  | _, _, .positive R S old next => by
      simp only [dictionary, SourceOnly.FiniteKernelLadder.Path.forward,
        LinearMap.id_comp, relabelEdge, positiveEdge, endpointMap,
        LinearMap.comp_assoc] <;> rfl
  | _, _, .comp u v => by
      rw [dictionary, Path.append_forward, dictionary_forward u, dictionary_forward v] <;> rfl

private theorem right_cast {n m : ℕ} (R : CountMat n m) (z : Fin n → ℤ) :
    (counts R).toLinearMapRight' (fun i => algebraMap ℤ D (z i)) =
      fun j => algebraMap ℤ D
        ((CountedMatrixBeamDiagram.integerCounts R).toLinearMapRight' z j) := by
  ext j
  simp only [Matrix.toLinearMapRight'_apply, Matrix.vecMul, counts,
    Matrix.map_apply, CountedMatrixBeamDiagram.integerCounts, dotProduct, map_sum, map_mul,
    Nat.castRingHom]
  rfl

/-- Exact finite coefficient equality with the existing B transport, before
passing to a colimit. Thus no injective-colimit shortcut is being used. -/
theorem endpointMap_cast : ∀ {F H : Presentation} (w : Word F H) (z : F.V → ℤ),
    endpointMap w (fun v => algebraMap ℤ D (z v)) =
      fun v => algebraMap ℤ D (PositiveWordBeamTransport.endpointMap w z v)
  | _, _, .relabel r, z => rfl
  | _, _, .positive R S old next, z => by
      change reindex next.vertex
        ((counts R).toLinearMapRight' (fun i => algebraMap ℤ D (z (old.vertex i)))) = _
      rw [right_cast]
      rfl
  | _, _, .comp u v, z => by
      change endpointMap v (endpointMap u (fun i => algebraMap ℤ D (z i))) = _
      rw [endpointMap_cast u z, endpointMap_cast v] <;> rfl


end SourceOnly.ActualWordMatrixPath
