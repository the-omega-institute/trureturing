/- GID: D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/MandalMannaDQDilworthRefutation.claim
   digest: Eight vertices give nonlocal distance-signless multiplicity above vicinal width. -/

/-
admission_basis: open-problem-resolution (#23915; Refuted).
Direct frozen dependencies: none (Mathlib imports only), for every declaration below.
Every row has escape_witness: none. All theorem proofs are bind-only after
expanding same-delivery helpers; definitions and instances supply their objects.
Vertices: proof_shape: bind-only; consumers: verticesFintype, reverseCGraph, cGraph, blockIndex, localExceptions, verticesComputableEq, vertex8, e8, distance8, chain8, u8, v8, mode8_independent, multiplicity8_ge.
verticesFintype: proof_shape: bind-only; consumers: localExceptions, claim, shift8_model.
reverseCGraph: proof_shape: bind-only; consumers: cGraph, reverseCGraphDecidable.
cGraph: proof_shape: bind-only; consumers: localExceptions, claim, universal8, connected8, distance8, chain8, dilworth8_le, dilworth8_eq, distanceCode8, distance8_table, shift8_model, eigen8_of_kernel, u8_mode, v8_mode, multiplicity8_ge, eigenvalue8, result.
blockIndex: proof_shape: bind-only; consumers: localExceptions.
transmission: proof_shape: bind-only; consumers: distanceSignless, localExceptions, shift8_model.
distanceSignless: proof_shape: bind-only; consumers: multiplicity, claim, shift8_model, eigen8_of_kernel, u8_mode, v8_mode, multiplicity8_ge, eigenvalue8.
vicinal: proof_shape: bind-only; consumers: HasChainCover.
HasChainCover: proof_shape: bind-only; consumers: dilworthNumber, chain8.
dilworthNumber: proof_shape: bind-only; consumers: claim, dilworth8_le, dilworth8_eq.
localExceptions: proof_shape: bind-only; consumers: claim, no_local8.
multiplicity: proof_shape: bind-only; consumers: claim, multiplicity8_ge, result.
claim: proof_shape: bind-only; consumers: result.
familyShift: proof_shape: bind-only; consumers: familyU_kernel, familyV_kernel, shift8_model, eigen8_of_kernel.
familyU: proof_shape: bind-only; consumers: familyU_kernel, family_independent, u8, eigenvalue8.
familyV: proof_shape: bind-only; consumers: familyV_kernel, family_independent, v8.
sum_below: proof_shape: bind-only; consumers: familyV_kernel.
sum_above: proof_shape: bind-only; consumers: familyV_kernel.
familyU_kernel: proof_shape: bind-only; consumers: u8_mode.
familyV_kernel: proof_shape: bind-only; consumers: v8_mode.
family_independent: proof_shape: bind-only; consumers: mode8_independent.
verticesComputableEq: proof_shape: bind-only; consumers: reverseCGraphDecidable, chain8.
reverseCGraphDecidable: proof_shape: bind-only; consumers: universal8, chain8, distanceCode8.
alpha8: proof_shape: bind-only; consumers: vertex8, e8, universal8, connected8, distance8, chain8, dilworth8_le, dilworth8_eq, no_local8, u8, v8, distanceCode8, distance8_table, shift8_model, eigen8_of_kernel, u8_mode, v8_mode, mode8_independent, multiplicity8_ge, eigenvalue8, result.
vertex8: proof_shape: bind-only; consumers: vertex8_bijective, e8, distanceCode8, distance8_table.
vertex8_bijective: proof_shape: bind-only; consumers: e8.
e8: proof_shape: bind-only; consumers: universal8, connected8, distance8, chain8, dilworth8_eq, u8, v8, distance8_table, shift8_model, eigen8_of_kernel, mode8_independent, eigenvalue8.
universal8: proof_shape: bind-only; consumers: connected8, distance8.
connected8: proof_shape: bind-only; consumers: distance8, result.
distance8: proof_shape: bind-only; consumers: distance8_table.
chain8: proof_shape: bind-only; consumers: dilworth8_le.
dilworth8_le: proof_shape: bind-only; consumers: dilworth8_eq.
dilworth8_eq: proof_shape: bind-only; consumers: result.
no_local8: proof_shape: bind-only; consumers: result.
label8: proof_shape: bind-only; consumers: label8_bijective, l8, l8_apply, shift8_model, eigenvalue8.
label8_bijective: proof_shape: bind-only; consumers: l8.
l8: proof_shape: bind-only; consumers: l8_apply, u8, v8, shift8_model, eigen8_of_kernel, mode8_independent, eigenvalue8.
l8_apply: proof_shape: bind-only; consumers: shift8_model.
u8: proof_shape: bind-only; consumers: u8_mode, mode8_independent, multiplicity8_ge, eigenvalue8.
v8: proof_shape: bind-only; consumers: v8_mode, mode8_independent, multiplicity8_ge.
distanceCode8: proof_shape: bind-only; consumers: distanceCode8_table.
distanceTable8: proof_shape: bind-only; consumers: distanceCode8_table, distance8_table, shift8_model.
distanceCode8_table: proof_shape: bind-only; consumers: distance8_table.
distance8_table: proof_shape: bind-only; consumers: shift8_model.
shift8_model: proof_shape: bind-only; consumers: eigen8_of_kernel.
eigen8_of_kernel: proof_shape: bind-only; consumers: u8_mode, v8_mode.
u8_mode: proof_shape: bind-only; consumers: multiplicity8_ge, eigenvalue8.
v8_mode: proof_shape: bind-only; consumers: multiplicity8_ge.
mode8_independent: proof_shape: bind-only; consumers: multiplicity8_ge.
multiplicity8_ge: proof_shape: bind-only; consumers: result.
eigenvalue8: proof_shape: bind-only; consumers: result.
result: proof_shape: bind-only; consumers: settling result.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The source recurrence uses SimpleGraph.sum and graph complement; distance,
root multiplicity and eigenspaces use the native Mathlib constructions.
The parameterized matrix kernels and independence are uniform; the native
graph identification, width and exclusion are proved at eight vertices only.
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Eigenspace.Zero

open Matrix
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


namespace D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation

/-- Vertices of successive disjoint unions, with the most recent block last in the sum. -/
def Vertices : List ℕ → Type
  | [] => PEmpty
  | a :: rest => Vertices rest ⊕ Fin a

private instance verticesFintype : (rev : List ℕ) → Fintype (Vertices rev)
  | [] => inferInstanceAs (Fintype PEmpty)
  | a :: rest => by
      change Fintype (Vertices rest ⊕ Fin a)
      letI := verticesFintype rest
      infer_instance

/-- Complement of the disjoint union with a complete graph; the empty stage is auxiliary. -/
def reverseCGraph : (rev : List ℕ) → SimpleGraph (Vertices rev)
  | [] => ⊥
  | a :: rest => ((reverseCGraph rest).sum (⊤ : SimpleGraph (Fin a)))ᶜ

/-- C(alpha_1,...,alpha_m) with the source's chronological list. -/
@[reducible] def cGraph (alpha : List ℕ) : SimpleGraph (Vertices alpha.reverse) :=
  reverseCGraph alpha.reverse

/-- The source's one-based block index. -/
def blockIndex : (rev : List ℕ) → Vertices rev → ℕ
  | [], v => nomatch v
  | _ :: rest, Sum.inl v => blockIndex rest v
  | _ :: rest, Sum.inr _ => rest.length + 1

/-- Transmission is the sum of native shortest-path distances. -/
noncomputable def transmission {V : Type} [Fintype V] (G : SimpleGraph V) (u : V) : ℝ :=
  ∑ v : V, (G.dist u v : ℝ)

/-- D^Q(G) = diag(Tr) + D(G). -/
noncomputable def distanceSignless {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Matrix V V ℝ :=
  Matrix.diagonal (transmission G) + Matrix.of (fun u v => (G.dist u v : ℝ))

/-- N(u) is contained in the closed neighborhood of v. -/
def vicinal {V : Type} (G : SimpleGraph V) (u v : V) : Prop :=
  G.neighborSet u ⊆ insert v (G.neighborSet v)

/-- A cover by k vicinal chains, represented by assigning each vertex a chain. -/
def HasChainCover {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, ∀ u v : V, c u = c v → vicinal G u v ∨ vicinal G v u

/-- Minimum chain-cover size in extended naturals: an empty feasible set has infimum infinity. -/
noncomputable def dilworthNumber {V : Type} (G : SimpleGraph V) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ HasChainCover G n}

/-- The block-dependent local values, only from source blocks of size at least two. -/
noncomputable def localExceptions (alpha : List ℕ) : Set ℝ :=
  {theta | ∃ i : Fin alpha.length, 2 ≤ alpha[i] ∧
    ∃ v : Vertices alpha.reverse, blockIndex alpha.reverse v = i.val + 1 ∧
      ((Odd (i.val + 1) ∧ theta = transmission (cGraph alpha) v - 1) ∨
       (Even (i.val + 1) ∧ theta = transmission (cGraph alpha) v - 2))}

/-- Algebraic multiplicity, using the native characteristic polynomial root multiplicity. -/
noncomputable def multiplicity {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (theta : ℝ) : ℕ :=
  Polynomial.rootMultiplicity theta (distanceSignless G).charpoly

/-- Conjecture 5.5, with the even-length convention of Section 2 and positive block sizes. -/
def claim : Prop := by
  classical
  exact ∀ (alpha : List ℕ), 2 ≤ alpha.length → Even alpha.length →
    (∀ i : Fin alpha.length, 0 < alpha[i]) →
    (cGraph alpha).Connected →
    ∀ (theta : ℝ),
      Module.End.HasEigenvalue (Matrix.toLin' (distanceSignless (cGraph alpha))) theta →
      theta ∉ localExceptions alpha →
      (multiplicity (cGraph alpha) theta : ℕ∞) ≤ dilworthNumber (cGraph alpha)




private def familyShift (R : ℕ) : Matrix ((Fin R ⊕ (Fin (R+1) ⊕ Fin (R+1)))) ((Fin R ⊕ (Fin (R+1) ⊕ Fin (R+1)))) ℝ
  | .inl x, .inl y => 1 + if x = y then 1 else 0
  | .inl _, .inr (.inl _) => 2
  | .inl _, .inr (.inr _) => 1
  | .inr (.inl _), .inl _ => 2
  | .inr (.inr _), .inl _ => 1
  | .inr (.inl i), .inr (.inl j) => 2 + if i = j then (R : ℝ) + i.val - 1 else 0
  | .inr (.inr i), .inr (.inr j) => 1 + if i = j then -(i.val : ℝ) else 0
  | .inr (.inl i), .inr (.inr j) => 1 + if j < i then 1 else 0
  | .inr (.inr i), .inr (.inl j) => 1 + if i < j then 1 else 0

private def familyU (R : ℕ) : (Fin R ⊕ (Fin (R+1) ⊕ Fin (R+1))) → ℝ
  | .inl _ => -1
  | .inr (.inl i) => if i = 0 then 1 else 0
  | .inr (.inr i) => if i = 0 then (R : ℝ) - 1 else 0

private def familyV (R : ℕ) : (Fin R ⊕ (Fin (R+1) ⊕ Fin (R+1))) → ℝ
  | .inl _ => 0
  | .inr (.inl i) => -1 + if i = 0 then 1 else 0
  | .inr (.inr i) => 1 + if i = 0 then (R : ℝ) - 1 else 0

private theorem sum_below {n : ℕ} (i : Fin n) :
    ((Finset.univ.filter (fun j : Fin n => j < i)).card : ℝ) = i.val := by
  have h : Finset.univ.filter (fun j : Fin n => j < i) = Finset.Iio i := by
    exact Finset.filter_gt_eq_Iio
  rw [h,Fin.card_Iio]

private theorem sum_above {n : ℕ} (i : Fin n) :
    ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℝ) = (n : ℝ) - 1 - i.val := by
  have h : Finset.univ.filter (fun j : Fin n => i < j) = Finset.Ioi i := by
    exact Finset.filter_lt_eq_Ioi
  rw [h,Fin.card_Ioi]
  have hn := i.isLt
  have hi : 1 ≤ n := Nat.one_le_of_lt hn
  have hi2 : i.val ≤ n - 1 := (Nat.le_sub_one_iff_lt hi).mpr hn
  rw [Nat.cast_sub hi2, Nat.cast_sub hi]
  norm_num

private theorem familyU_kernel (R : ℕ) : familyShift R *ᵥ familyU R = 0 := by
  ext x
  rcases x with x | (i | i)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyU,
      mul_ite, Finset.sum_add_distrib]
    <;> ring
  · by_cases hi : i = 0
    · subst i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyU,
        mul_ite]
      <;> ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyU,
        add_mul, ite_mul, mul_ite, hi,
        show (0 : Fin (R+1)) < i from Fin.pos_iff_ne_zero.mpr hi]
      <;> ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyU,
      add_mul, ite_mul, mul_ite]
    split_ifs <;> simp_all <;> ring

private theorem familyV_kernel (R : ℕ) : familyShift R *ᵥ familyV R = 0 := by
  ext x
  rcases x with x | (i | i)
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyV,
      add_mul, mul_add, mul_ite, Finset.sum_add_distrib]
    <;> ring
  · by_cases hi : i = 0
    · subst i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyV,
        add_mul, mul_add, mul_ite, Finset.sum_add_distrib,
]
      <;> ring
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyV,
        add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib,
        sum_below, hi, show (0 : Fin (R+1)) < i from Fin.pos_iff_ne_zero.mpr hi]
      <;> ring
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, familyShift, familyV,
      add_mul, mul_add, ite_mul, mul_ite, Finset.sum_add_distrib,
      sum_above]
    split_ifs <;> simp_all <;> ring


private theorem family_independent (R : ℕ) (hR : 1 ≤ R) :
    LinearIndependent ℝ (![familyU R,familyV R] : Fin 2 → (Fin R ⊕ (Fin (R+1) ⊕ Fin (R+1))) → ℝ) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have hh := congrFun h (.inr (.inl ⟨1,by omega⟩))
    norm_num [familyV] at hh
  · intro a h
    have hh := congrFun h (.inl ⟨0,by omega⟩)
    norm_num [familyV,familyU] at hh



private def verticesComputableEq : (rev : List ℕ) → DecidableEq (Vertices rev)
  | [] => inferInstanceAs (DecidableEq PEmpty)
  | _ :: rest => by
      change DecidableEq (Vertices rest ⊕ _)
      letI := verticesComputableEq rest
      infer_instance

private instance reverseCGraphDecidable : (rev : List ℕ) → DecidableRel (reverseCGraph rev).Adj
  | [] => inferInstanceAs (DecidableRel (⊥ : SimpleGraph PEmpty).Adj)
  | a :: rest => by
      letI := verticesComputableEq rest
      letI := reverseCGraphDecidable rest
      letI : DecidableRel ((reverseCGraph rest).sum (⊤ : SimpleGraph (Fin a))).Adj := by
        intro u v
        cases u <;> cases v <;> dsimp [SimpleGraph.sum] <;> infer_instance
      change DecidableRel ((reverseCGraph rest).sum (⊤ : SimpleGraph (Fin a)))ᶜ.Adj
      infer_instance


private def alpha8 : List ℕ := [1,1,1,1,1,1,1,1]


private def vertex8 : Fin 8 → (Vertices alpha8.reverse) := ![
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr 0))))))),
  .inl (.inl (.inl (.inl (.inl (.inl (.inr 0)))))),
  .inl (.inl (.inl (.inl (.inl (.inr 0))))),
  .inl (.inl (.inl (.inl (.inr 0)))),
  .inl (.inl (.inl (.inr 0))),
  .inl (.inl (.inr 0)),
  .inl (.inr 0),
  .inr 0]

private theorem vertex8_bijective : Function.Bijective vertex8 := by
  exact (Multiset.bijective_iff_map_univ_eq_univ vertex8).mpr rfl

private noncomputable def e8 : Fin 8 ≃ (Vertices alpha8.reverse) := Equiv.ofBijective vertex8 vertex8_bijective


private theorem universal8 : ∀ i : Fin 8, i ≠ 7 → (cGraph alpha8).Adj (e8 i) (e8 7) := by

  decide

private theorem connected8 : (cGraph alpha8).Connected := by
  apply (SimpleGraph.connected_iff (cGraph alpha8)).mpr
  refine ⟨?_, ⟨e8 7⟩⟩
  intro u v
  obtain ⟨i,rfl⟩ := e8.surjective u
  obtain ⟨j,rfl⟩ := e8.surjective v
  have reach : ∀ i : Fin 8, (cGraph alpha8).Reachable (e8 i) (e8 7) := by
    intro i
    by_cases hi : i = 7
    · subst i; exact .rfl
    · exact (universal8 i hi).reachable
  exact (reach i).trans (reach j).symm

private theorem distance8 (u v : (Vertices alpha8.reverse)) :
    (cGraph alpha8).dist u v = if u = v then 0 else if (cGraph alpha8).Adj u v then 1 else 2 := by
  split_ifs with huv hadj
  · subst v; exact SimpleGraph.dist_self
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  · have hu : u ≠ e8 7 := by
      intro h; subst u
      obtain ⟨j,rfl⟩ := e8.surjective v
      exact hadj ((universal8 j (fun hj => huv (by rw [hj]))).symm)
    have hv : v ≠ e8 7 := by
      intro h; subst v
      obtain ⟨i,rfl⟩ := e8.surjective u
      exact hadj (universal8 i (fun hi => huv (by rw [hi])))
    have huadj : (cGraph alpha8).Adj u (e8 7) := by
      obtain ⟨i,rfl⟩ := e8.surjective u
      exact universal8 i (fun hi => hu (by rw [hi]))
    have hvadj : (cGraph alpha8).Adj (e8 7) v := by
      obtain ⟨i,rfl⟩ := e8.surjective v
      exact (universal8 i (fun hi => hv (by rw [hi]))).symm
    apply Nat.le_antisymm
    · exact SimpleGraph.dist_le (SimpleGraph.Walk.cons huadj (.cons hvadj .nil))
    · exact connected8.one_lt_dist_of_ne_of_not_adj huv hadj

private theorem chain8 : HasChainCover (cGraph alpha8) 1 := by
  letI := verticesComputableEq alpha8.reverse
  refine ⟨fun _ => 0, ?_⟩
  have h : ∀ i j : Fin 8,
      (∀ w : (Vertices alpha8.reverse), (cGraph alpha8).Adj (e8 i) w → w = e8 j ∨ (cGraph alpha8).Adj (e8 j) w) ∨
      (∀ w : (Vertices alpha8.reverse), (cGraph alpha8).Adj (e8 j) w → w = e8 i ∨ (cGraph alpha8).Adj (e8 i) w) := by

    decide
  intro u v _
  obtain ⟨i,rfl⟩ := e8.surjective u
  obtain ⟨j,rfl⟩ := e8.surjective v
  exact h i j

private theorem dilworth8_le : dilworthNumber (cGraph alpha8) ≤ 1 := by
  exact sInf_le ⟨1, rfl, chain8⟩

private theorem dilworth8_eq : dilworthNumber (cGraph alpha8) = 1 := by
  apply le_antisymm dilworth8_le
  apply le_sInf
  rintro k ⟨n,rfl,⟨c,hc⟩⟩
  rcases n with _ | n
  · exact Fin.elim0 (c (e8 0))
  · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

private theorem no_local8 : (8 : ℝ) ∉ localExceptions alpha8 := by
  rintro ⟨i, hi, _⟩
  have h : alpha8[i] = 1 := by fin_cases i <;> rfl
  omega


private def label8 : Fin 8 → (Fin 2 ⊕ (Fin 3 ⊕ Fin 3)) := ![
  .inl 0, .inl 1, .inr (.inl 0), .inr (.inr 0),
  .inr (.inl 1), .inr (.inr 1), .inr (.inl 2), .inr (.inr 2)]

private theorem label8_bijective : Function.Bijective label8 := by
  decide

private noncomputable def l8 : Fin 8 ≃ (Fin 2 ⊕ (Fin 3 ⊕ Fin 3)) := Equiv.ofBijective label8 label8_bijective

private theorem l8_apply (i : Fin 8) : l8 i = label8 i := rfl

private noncomputable def u8 : (Vertices alpha8.reverse) → ℝ := fun w => familyU 2 (l8 (e8.symm w))
private noncomputable def v8 : (Vertices alpha8.reverse) → ℝ := fun w => familyV 2 (l8 (e8.symm w))

private def distanceCode8 (i j : Fin 8) : ℕ :=
  if i = j then 0 else if (cGraph alpha8).Adj (vertex8 i) (vertex8 j) then 1 else 2

private def distanceTable8 : Fin 8 → Fin 8 → ℕ := ![
  ![0,1,2,1,2,1,2,1], ![1,0,2,1,2,1,2,1],
  ![2,2,0,1,2,1,2,1], ![1,1,1,0,2,1,2,1],
  ![2,2,2,2,0,1,2,1], ![1,1,1,1,1,0,2,1],
  ![2,2,2,2,2,2,0,1], ![1,1,1,1,1,1,1,0]]

private theorem distanceCode8_table : ∀ i j : Fin 8,
    distanceCode8 i j = distanceTable8 i j := by decide

private theorem distance8_table (i j : Fin 8) :
    (cGraph alpha8).dist (e8 i) (e8 j) = distanceTable8 i j := by
  rw [distance8]
  simp only [e8.injective.eq_iff]
  change (if i = j then 0 else if (cGraph alpha8).Adj (vertex8 i) (vertex8 j) then 1 else 2) = _
  exact distanceCode8_table i j

private theorem shift8_model (i j : Fin 8) :
    distanceSignless (cGraph alpha8) (e8 i) (e8 j) =
      familyShift 2 (l8 i) (l8 j) + 8 * (if i=j then 1 else 0) := by
  simp only [distanceSignless, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.of_apply, transmission]
  rw [← e8.sum_comp]
  simp only [e8.injective.eq_iff]
  simp_rw [distance8_table]
  simp only [l8_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [distanceTable8, label8, familyShift, Fin.sum_univ_succ]

private theorem eigen8_of_kernel (z : (Fin 2 ⊕ (Fin 3 ⊕ Fin 3)) → ℝ)
    (hz : familyShift 2 *ᵥ z = 0) :
    distanceSignless (cGraph alpha8) *ᵥ (fun w => z (l8 (e8.symm w))) =
      (8 : ℝ) • (fun w => z (l8 (e8.symm w))) := by
  ext w
  obtain ⟨i,rfl⟩ := e8.surjective w
  have hrow := congrFun hz (l8 i)
  change (∑ x, familyShift 2 (l8 i) x * z x) = 0 at hrow
  rw [← l8.sum_comp] at hrow
  change (∑ x, distanceSignless (cGraph alpha8) (e8 i) x * z (l8 (e8.symm x))) = _
  rw [← e8.sum_comp]
  simp only [e8.symm_apply_apply, shift8_model, add_mul, Finset.sum_add_distrib]
  rw [hrow, zero_add]
  simp [mul_ite, ite_mul]

private theorem u8_mode : distanceSignless (cGraph alpha8) *ᵥ u8 = (8 : ℝ) • u8 := by
  exact eigen8_of_kernel _ (familyU_kernel 2)

private theorem v8_mode : distanceSignless (cGraph alpha8) *ᵥ v8 = (8 : ℝ) • v8 := by
  exact eigen8_of_kernel _ (familyV_kernel 2)

private theorem mode8_independent : LinearIndependent ℝ (![u8,v8] : Fin 2 → (Vertices alpha8.reverse) → ℝ) := by
  let T := LinearMap.funLeft ℝ ℝ (fun w => l8 (e8.symm w))
  have hT : Function.Injective T :=
    LinearMap.funLeft_injective_of_surjective ℝ ℝ _
      (l8.surjective.comp e8.symm.surjective)
  have hli := (family_independent 2 (by decide)).map' T (LinearMap.ker_eq_bot.mpr hT)
  convert hli using 1
  ext i w
  fin_cases i <;> rfl

private theorem multiplicity8_ge : 2 ≤ multiplicity (cGraph alpha8) 8 := by
  classical
  let f : Module.End ℝ ((Vertices alpha8.reverse) → ℝ) := (distanceSignless (cGraph alpha8)).toLin'
  let E := f.eigenspace 8
  have hu : u8 ∈ E := Module.End.mem_eigenspace_iff.mpr u8_mode
  have hv : v8 ∈ E := Module.End.mem_eigenspace_iff.mpr v8_mode
  let modes : Fin 2 → E := ![⟨u8,hu⟩,⟨v8,hv⟩]
  have hi : LinearIndependent ℝ modes := by
    apply LinearIndependent.of_comp E.subtype
    convert mode8_independent using 1
    ext i w
    fin_cases i <;> rfl
  have hdim : 2 ≤ Module.finrank ℝ E := by
    simpa using hi.fintype_card_le_finrank
  have halg := LinearMap.finrank_eigenspace_le f 8
  rw [Matrix.charpoly_toLin'] at halg
  exact hdim.trans halg

private theorem eigenvalue8 : Module.End.HasEigenvalue (distanceSignless (cGraph alpha8)).toLin' (8 : ℝ) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := u8)
  refine ⟨Module.End.mem_eigenspace_iff.mpr u8_mode, ?_⟩
  intro h
  have hh := congrFun h (e8 0)
  norm_num [u8, familyU, l8, label8] at hh

theorem result : ¬ claim := by
  intro h
  have bound := h alpha8 (by decide) (by decide)
    (by intro i; fin_cases i <;> decide) connected8 8 eigenvalue8 no_local8
  have upper := bound.trans dilworth8_eq.le
  have lower : (2 : ℕ∞) ≤ (multiplicity (cGraph alpha8) 8 : ℕ∞) := by
    exact_mod_cast multiplicity8_ge
  have impossible : (2 : ℕ∞) ≤ 1 := lower.trans upper
  norm_num at impossible

end D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation
