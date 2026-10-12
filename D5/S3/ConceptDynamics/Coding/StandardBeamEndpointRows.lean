/- GID: D5/S3/ConceptDynamics/Coding/StandardBeamEndpointRows
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/StandardBeamEndpointRows
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Endpoint multiplicities of intrinsic ray partitions and numbered refinement. -/
import D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.StandardBeamGeometry
open scoped BigOperators Matrix

universe u v
variable {V : Type u} {E : Type v} (G : DirectedMultigraph V E)
variable [Fintype V] [Fintype E] [DecidableEq V]
variable (hG : Essential G)

/-- Sum over numbered outgoing edges, rather than a set of endpoints. -/
def adjacency : Matrix V V ℤ := fun u =>
  ∑ e : Out G u, Pi.single (G.target e.val) 1

def wordRow (u : V) (r : ℕ) : V → ℤ :=
  ∑ p : Continuation G u r, Pi.single (continuationEnd G p) 1

def endpointRow (U : Set (History G)) (n : ℤ) [Finite (Parts G U n)] : V → ℤ := by
  letI : Fintype (Parts G U n) := Fintype.ofFinite _
  exact ∑ P : Parts G U n, Pi.single (RayAt.endpoint G P.val) 1

lemma sum_vecMul {I : Type*} [Fintype I] (v : I → V → ℤ) (B : Matrix V V ℤ) :
    (∑ i, v i) ᵥ* B = ∑ i, (v i) ᵥ* B := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Finset.sum_apply]
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

@[simp] theorem wordRow_zero (u : V) : wordRow G u 0 = Pi.single u 1 := by
  change (∑ _p : PUnit, (Pi.single u (1 : ℤ) : V → ℤ)) =
    (Pi.single u 1 : V → ℤ)
  exact Fintype.sum_unique _

theorem wordRow_succ (u : V) (r : ℕ) :
    wordRow G u (r + 1) = ∑ e : Out G u, wordRow G (G.target e.val) r := by
  change (∑ p : (Σ e : Out G u, Continuation G (G.target e.val) r),
    (Pi.single (continuationEnd G p.2) (1 : ℤ) : V → ℤ)) = _
  exact Fintype.sum_sigma' (fun (e : Out G u) p =>
    (Pi.single (continuationEnd G p) (1 : ℤ) : V → ℤ))

/-- True right-row recurrence, obtained from actual edge-word numbering. -/
theorem wordRow_eq_pow (u : V) (r : ℕ) :
    wordRow G u r = (Pi.single u 1) ᵥ* (adjacency G ^ r) := by
  induction r generalizing u with
  | zero => simp
  | succ r ih =>
    rw [wordRow_succ]
    simp_rw [ih]
    rw [← sum_vecMul]
    have hone : (∑ e : Out G u, Pi.single (G.target e.val) (1 : ℤ)) =
        (Pi.single u 1) ᵥ* adjacency G := by
      simp [Matrix.single_vecMul, Matrix.row, adjacency]
    rw [hone, Matrix.vecMul_vecMul, ← pow_succ']

/-- Numbering the intrinsic common refinement by the numbered continuations
of EACH earlier actual ray, without collapsing repeated endpoints. -/
def refinementNumbering {U : Set (History G)} {n : ℤ} (hU : AtCut G U n) (r : ℕ) :
    (Σ P : Parts G U n, Continuation G (RayAt.endpoint G P.val) r) ≃
      Parts G U (n + (r : ℤ)) :=
  (Equiv.sigmaCongrRight (fun P : Parts G U n =>
    (rayPartsEquiv G hG (RayAt.representative G P.val) n r).trans
      (Equiv.subtypeEquivRight (fun Q => by rw [RayAt.set_eq G P.val])))).trans
    (partsRefinementEquiv G hU (by omega))

theorem refinementNumbering_endpoint {U : Set (History G)} {n : ℤ}
    (hU : AtCut G U n) (r : ℕ)
    (P : Σ P : Parts G U n, Continuation G (RayAt.endpoint G P.val) r) :
    RayAt.endpoint G ((refinementNumbering G hG hU r P).val) =
      continuationEnd G P.2 := by
  change RayAt.endpoint G
    (rayAt G (refined G hG (RayAt.representative G P.1.val) n r P.2) _) = _
  exact (RayAt.endpoint_of_mem G _ _ (self_mem_ray G _ _)).trans
    (refined_endpoint G hG _ n r P.2)

/-- c_(n+r)=c_n B^r for the intrinsic partitions of the SAME actual set. -/
theorem endpointRow_refine {U : Set (History G)} {n : ℤ} (hU : AtCut G U n) (r : ℕ) :
    letI : Finite (Parts G U n) := hU.1
    letI : Finite (Parts G U (n + (r : ℤ))) := (atCut_mono G hG hU (by omega)).1
    endpointRow G U (n + (r : ℤ)) = endpointRow G U n ᵥ* adjacency G ^ r := by
  letI : Finite (Parts G U n) := hU.1
  letI : Finite (Parts G U (n + (r : ℤ))) := (atCut_mono G hG hU (by omega)).1
  letI : Fintype (Parts G U n) := Fintype.ofFinite _
  letI : Fintype (Parts G U (n + (r : ℤ))) := Fintype.ofFinite _
  change (∑ Q : Parts G U (n + (r : ℤ)), Pi.single (RayAt.endpoint G Q.val) 1) = _
  have he := Fintype.sum_equiv (refinementNumbering G hG hU r)
    (fun P => (Pi.single (continuationEnd G P.2) (1 : ℤ) : V → ℤ))
    (fun Q => (Pi.single (RayAt.endpoint G Q.val) (1 : ℤ) : V → ℤ))
    (fun P => congrArg (fun u : V => Pi.single u (1 : ℤ))
      (refinementNumbering_endpoint G hG hU r P).symm)
  rw [← he, Fintype.sum_sigma]
  change (∑ P : Parts G U n, wordRow G (RayAt.endpoint G P.val) r) = _
  simp_rw [wordRow_eq_pow]
  rw [← sum_vecMul]
  rfl

/-- A finite DISJOINT same-cut union has exactly those ray pieces.
This theorem fails for an overlapping union, which is deliberately excluded. -/
def disjointUnionPartsEquiv {I : Type*} [Fintype I] (beta : I → History G) (n : ℤ)
    (hd : ∀ i j, i ≠ j → Disjoint (ray G (beta i) n) (ray G (beta j) n)) :
    I ≃ Parts G (⋃ i, ray G (beta i) n) n := by
  let f : I → Parts G (⋃ i, ray G (beta i) n) n := fun i =>
    ⟨rayAt G (beta i) n, by
      change ray G (beta i) n ⊆ ⋃ i, ray G (beta i) n
      exact Set.subset_iUnion (fun i : I => ray G (beta i) n) i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    by_contra hij
    have hsets := congrArg (fun P => P.val.val) he
    change ray G (beta i) n = ray G (beta j) n at hsets
    apply Set.disjoint_left.mp (hd i j hij) (self_mem_ray G (beta i) n)
    rw [← hsets]
    exact self_mem_ray G (beta i) n
  · intro P
    obtain ⟨x, hx⟩ := RayAt.nonempty G P.val
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (P.property hx)
    exact ⟨i, Subtype.ext (RayAt.eq_of_inter G _ _ x hi hx)⟩

/-- A concrete finite ray decomposition therefore determines the integer row,
with one basis contribution per numbered component. -/
theorem endpointRow_disjointUnion {I : Type*} [Fintype I] (beta : I → History G) (n : ℤ)
    (hd : ∀ i j, i ≠ j → Disjoint (ray G (beta i) n) (ray G (beta j) n)) :
    letI : Finite (Parts G (⋃ i, ray G (beta i) n) n) :=
      (atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)).1
    endpointRow G (⋃ i, ray G (beta i) n) n =
      ∑ i, Pi.single (endpoint G (beta i) n) (1 : ℤ) := by
  letI : Finite (Parts G (⋃ i, ray G (beta i) n) n) :=
    (atCut_iUnion G _ n (fun i => ray_atCut G hG (beta i) n)).1
  letI : Fintype (Parts G (⋃ i, ray G (beta i) n) n) := Fintype.ofFinite _
  unfold endpointRow
  exact (Fintype.sum_equiv (disjointUnionPartsEquiv G beta n hd)
    (fun i => (Pi.single (endpoint G (beta i) n) (1 : ℤ) : V → ℤ))
    (fun P => (Pi.single (RayAt.endpoint G P.val) (1 : ℤ) : V → ℤ)) (fun i => by
      change (Pi.single (endpoint G (beta i) n) (1 : ℤ) : V → ℤ) =
        (Pi.single (RayAt.endpoint G (rayAt G (beta i) n)) (1 : ℤ) : V → ℤ)
      exact congrArg (fun u : V => (Pi.single u (1 : ℤ) : V → ℤ))
        (RayAt.endpoint_of_mem G (rayAt G (beta i) n) (beta i)
          (self_mem_ray G (beta i) n)).symm)).symm

/-- A single actual ray contributes one vertex, with its full past retained. -/
theorem endpointRow_ray (alpha : History G) (n : ℤ) :
    letI : Finite (Parts G (ray G alpha n) n) := (ray_atCut G hG alpha n).1
    endpointRow G (ray G alpha n) n = Pi.single (endpoint G alpha n) 1 := by
  letI : Finite (Parts G (ray G alpha n) n) := (ray_atCut G hG alpha n).1
  let P : Parts G (ray G alpha n) n := ⟨rayAt G alpha n, Set.Subset.rfl⟩
  have hP (Q : Parts G (ray G alpha n) n) : Q = P := by
    obtain ⟨x, hx⟩ := RayAt.nonempty G Q.val
    exact Subtype.ext (RayAt.eq_of_inter G Q.val P.val x hx (Q.property hx))
  letI : Subsingleton (Parts G (ray G alpha n) n) :=
    ⟨fun Q R => (hP Q).trans (hP R).symm⟩
  letI : Fintype (Parts G (ray G alpha n) n) := Fintype.ofFinite _
  unfold endpointRow
  rw [Fintype.sum_subsingleton _ P]
  exact congrArg (fun u : V => (Pi.single u (1 : ℤ) : V → ℤ))
    (RayAt.endpoint_of_mem G (rayAt G alpha n) alpha (self_mem_ray G alpha n))

end D5.S3.ConceptDynamics.Coding.StandardBeamEndpointRows
