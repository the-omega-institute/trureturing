/- GID: D5/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample.claimPhys; result=D5/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample.result; claim=D5/S3/Zeros/LeeYang/QuiverTreePhysicalCounterexample.claimPhys
   digest: The all-vertex physical tree Lee-Yang counterexample at tau minus one. -/

import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

open scoped BigOperators
open Finset Polynomial Complex
open scoped ComplexConjugate

namespace D5.S3.Zeros.LeeYang.QuiverTreePhysicalCounterexample

open QuiverTreeIsingRefutation
open D5.S3.Observer.AgencyHolonomy.NamedTreePhaseTransport

/-- The endpoint factor in FMR equation (2.15), with factorials cast before division. -/
noncomputable def endpointFactor (t : ℕ) : ℝ :=
  (Nat.factorial (2 * t) : ℝ) /
    ((Nat.factorial (t - 1) : ℝ) * (Nat.factorial t : ℝ))

/-- Incidence valence, counting both endpoint roles. -/
def valence {V E : Type} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (v : V) : ℕ :=
  (univ.filter fun e => src e = v).card + (univ.filter fun e => tgt e = v).card

/-- Original all-vertex correlator factor. On legal splits, mass is at least valence,
so the natural factorial argument agrees with the paper's integer expression. -/
noncomputable def vertexFactor {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (n k : E → ℕ) (v : V) : ℝ :=
  (Nat.factorial (mass src tgt n k v - 1) : ℝ) /
    (Nat.factorial (mass src tgt n k v - valence src tgt v + 2) : ℝ) *
    ((∏ e ∈ univ.filter (fun e => src e = v), endpointFactor (k e)) *
      ∏ e ∈ univ.filter (fun e => tgt e = v), endpointFactor (n e - k e))

/-- Physical rho: every labelled edge binomial and every vertex factor are present.
This is the preregistered all-vertex editorial reading of (2.31); the displayed
paper upper limit is m, while its construction and (2.16)--(2.19) use m+1. -/
noncomputable def physicalRho {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (src tgt : E → V) (n k : E → ℕ) : ℝ :=
  (∏ e, (Nat.choose (2 * n e) (2 * k e) : ℝ)) *
    ∏ v, vertexFactor src tgt n k v

/-- Primary FMR-P registration, issue #17677: every finite tree with at least two
edges, fixed labelled totals at least two, actual all-vertex weights, tau=-1. -/
def claimPhys : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V), NamedSpanningTree src tgt Set.univ →
    2 ≤ Fintype.card E → ∀ (n : E → ℕ), (∀ e, 2 ≤ n e) → ∀ z : ℂ,
      ((treePoly src tgt n (physicalRho src tgt n) (-1)).map
        (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1

/-- Two hubs, each with sixty leaves. None is the central vertex. -/
private abbrev Edge := Bool × Option (Fin 60)
private abbrev Vertex := Option Edge

/-- Native arrows reverse every paper arrow, preserving k at the same endpoint. -/
private def src (e : Edge) : Vertex := some e
private def tgt (e : Edge) : Vertex := match e.2 with
  | none => none
  | some _ => some (e.1, none)
private def totals (e : Edge) : ℕ := match e.2 with
  | none => 3
  | some _ => 2

/-- Four labelled splits; pendant coordinates are forced to one. -/
private def split (a b : ℕ) (e : Edge) : ℕ := match e.2 with
  | none => if e.1 then b else a
  | some _ => 1

private noncomputable def physicalScalar : ℝ :=
  900 * (Nat.factorial 60 : ℝ)^2 * 12^120

private noncomputable def geom (m : ℕ) : Polynomial ℝ := ∑ j ∈ range m, X^j
private noncomputable def obstruction : Polynomial ℝ :=
  7442 * geom 62 ^ 2 * (1 + X^2) +
  488 * geom 62 * geom 61 * (1 + X^3) +
  9 * geom 61 ^ 2 * (1 + X^4)

private theorem legal_parts {E : Type} [Fintype E] [DecidableEq E]
    (n : E → ℕ) (hn : ∀ e, 2 ≤ n e) (k : E → ℕ) (hk : k ∈ splits n) (e : E) :
    1 ≤ k e ∧ 1 ≤ n e - k e ∧ k e ≤ n e := by
  have h := Fintype.mem_piFinset.mp hk e
  have he := Finset.mem_Icc.mp h
  have hne := hn e
  omega

private theorem totals_admissible (e : Edge) : 2 ≤ totals e := by
  rcases e with ⟨b, _ | i⟩ <;> simp [totals]

private theorem nonloop (e : Edge) : src e ≠ tgt e := by
  rcases e with ⟨b, _ | i⟩ <;> simp [src, tgt]

private theorem edge_injective : Function.Injective (fun e : Edge => s(src e, tgt e)) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Option.some.inj h.1
  · rcases e with ⟨b, _ | i⟩ <;> rcases f with ⟨c, _ | j⟩ <;>
      simp [src, tgt] at h

private theorem tree_ok : NamedSpanningTree src tgt Set.univ := by
  classical
  let G := treeSupport src tgt Set.univ
  have adj (e : Edge) : G.Adj (src e) (tgt e) := by
    exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨⟨e, Set.mem_univ _⟩, rfl⟩, nonloop e⟩
  have connected : G.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).mpr
    refine ⟨none, ?_⟩
    rintro (_ | ⟨b, _ | i⟩)
    · exact SimpleGraph.Reachable.rfl
    · exact (adj (b, none)).symm.reachable
    · exact ((adj (b, none)).symm.reachable).trans ((adj (b, some i)).symm.reachable)
  have edge_membership (e : Edge) : s(src e, tgt e) ∈ G.edgeSet := by
    exact G.mem_edgeSet.mpr (adj e)
  let edgeEquiv : Edge ≃ G.edgeSet := Equiv.ofBijective
    (fun e => ⟨s(src e, tgt e), edge_membership e⟩) (by
      constructor
      · intro e f h
        exact edge_injective (congrArg Subtype.val h)
      · rintro ⟨q, hq⟩
        have hq' : q ∈ Set.range (fun e : (Set.univ : Set Edge) => s(src e, tgt e)) := by
          exact (show q ∈ Set.range (fun e : (Set.univ : Set Edge) => s(src e, tgt e)) \
            Sym2.diagSet from by simpa [G, treeSupport, SimpleGraph.edgeSet_fromEdgeSet] using hq).1
        obtain ⟨e, he⟩ := hq'
        exact ⟨e.val, Subtype.ext he⟩)
  refine ⟨fun e he => nonloop e, ?_, ?_⟩
  · intro e f h
    exact Subtype.ext (edge_injective h)
  · apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨connected, ?_⟩
    rw [← Nat.card_congr edgeEquiv]
    norm_num [Vertex, Edge]

private theorem split_legal (a b : ℕ) (ha : a = 1 ∨ a = 2) (hb : b = 1 ∨ b = 2) :
    split a b ∈ splits totals := by
  apply Fintype.mem_piFinset.mpr
  rintro ⟨c, _ | i⟩
  · cases c <;> simp [totals, split, Finset.mem_Icc] <;> omega
  · simp [totals, split]

private theorem four_splits : splits totals =
    {split 1 1, split 1 2, split 2 1, split 2 2} := by
  ext k
  constructor
  · intro hk
    have ha := legal_parts totals totals_admissible k hk (false, none)
    have hb := legal_parts totals totals_admissible k hk (true, none)
    have ha' : k (false, none) = 1 ∨ k (false, none) = 2 := by
      simp [totals] at ha
      omega
    have hb' : k (true, none) = 1 ∨ k (true, none) = 2 := by
      simp [totals] at hb
      omega
    have he : k = split (k (false, none)) (k (true, none)) := by
      funext e
      rcases e with ⟨b, _ | i⟩
      · cases b <;> rfl
      · have h := legal_parts totals totals_admissible k hk (b, some i)
        simp [totals] at h
        simp [split]
        omega
    rw [he]
    rcases ha' with h | h <;> rcases hb' with h' | h' <;> simp [h, h']
  · intro hk
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      exact split_legal _ _ (by omega) (by omega)

private theorem mass_centre (a b : ℕ) :
    mass src tgt totals (split a b) none = (3 - a) + (3 - b) := by
  unfold mass
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option,
    Fintype.sum_bool]
  simp [src, tgt, totals, split, Nat.add_comm]

private theorem mass_hub (a b : ℕ) (c : Bool) :
    mass src tgt totals (split a b) (some (c, none)) =
      60 + if c then b else a := by
  unfold mass
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option,
    Fintype.sum_bool]
  cases c <;> simp [src, tgt, totals, split, Nat.add_comm]

private theorem mass_leaf (a b : ℕ) (c : Bool) (i : Fin 60) :
    mass src tgt totals (split a b) (some (c, some i)) = 1 := by
  unfold mass
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_option,
    Fintype.sum_bool]
  cases c <;> simp [src, tgt, totals, split]

private theorem valence_centre : valence src tgt none = 2 := by
  unfold valence
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_option, Fintype.sum_bool]
  simp [src, tgt]

private theorem valence_hub (c : Bool) : valence src tgt (some (c, none)) = 61 := by
  unfold valence
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_option, Fintype.sum_bool]
  cases c <;> simp [src, tgt]

private theorem valence_leaf (c : Bool) (i : Fin 60) :
    valence src tgt (some (c, some i)) = 1 := by
  unfold valence
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_option, Fintype.sum_bool]
  cases c <;> simp [src, tgt]

private theorem vertex_leaf (a b : ℕ) (c : Bool) (i : Fin 60) :
    vertexFactor src tgt totals (split a b) (some (c, some i)) = 1 := by
  rw [vertexFactor, mass_leaf, valence_leaf]
  simp only [Finset.prod_filter, Fintype.prod_prod_type, Fintype.prod_option,
    Fintype.prod_bool]
  cases c <;> norm_num [src, tgt, totals, split, endpointFactor]

private theorem vertex_hub (a b : ℕ) (c : Bool) :
    vertexFactor src tgt totals (split a b) (some (c, none)) =
      (Nat.factorial (60 + (if c then b else a) - 1) : ℝ) /
        (Nat.factorial (60 + (if c then b else a) - 61 + 2) : ℝ) *
          (endpointFactor (if c then b else a) * 2^60) := by
  rw [vertexFactor, mass_hub, valence_hub]
  simp only [Finset.prod_filter, Fintype.prod_prod_type, Fintype.prod_option,
    Fintype.prod_bool]
  cases c <;> simp [src, tgt, totals, split, endpointFactor]

private theorem vertex_centre (a b : ℕ) :
    vertexFactor src tgt totals (split a b) none =
      (Nat.factorial ((3-a)+(3-b)-1) : ℝ) /
        (Nat.factorial ((3-a)+(3-b)-2+2) : ℝ) *
          (endpointFactor (3-a) * endpointFactor (3-b)) := by
  rw [vertexFactor, mass_centre, valence_centre]
  simp only [Finset.prod_filter, Fintype.prod_prod_type, Fintype.prod_option,
    Fintype.prod_bool]
  simp [src, tgt, totals, split, mul_comm]

private theorem physical_weight_expansion (a b : ℕ) :
    physicalRho src tgt totals (split a b) =
      ((Nat.choose 6 (2*a) : ℝ) * (Nat.choose 6 (2*b) : ℝ) * 6^120) *
        (vertexFactor src tgt totals (split a b) none *
          vertexFactor src tgt totals (split a b) (some (false, none)) *
          vertexFactor src tgt totals (split a b) (some (true, none))) := by
  unfold physicalRho
  simp [totals, split, Fintype.prod_prod_type, Fintype.prod_option,
    Fintype.prod_bool, vertex_leaf]
  norm_num [Nat.choose]
  ring

private theorem physical_weights :
    physicalRho src tgt totals (split 1 1) = 9 * physicalScalar ∧
    physicalRho src tgt totals (split 1 2) = 244 * physicalScalar ∧
    physicalRho src tgt totals (split 2 1) = 244 * physicalScalar ∧
    physicalRho src tgt totals (split 2 2) = 7442 * physicalScalar := by
  norm_num [physical_weight_expansion, vertex_centre, vertex_hub, endpointFactor,
    physicalScalar, Nat.factorial, Nat.choose]

private theorem geom_one (m : ℕ) : (geom m).eval 1 = m := by
  simp [geom]

private theorem obstruction_one : obstruction.eval 1 = 60972306 := by
  norm_num [obstruction, geom_one]

private def spinSign (b : Bool) : ℝ := if b then -1 else 1

private theorem sign_by_vertices {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (s t : E → V) (st : V → Bool) :
    (-1 : ℝ) ^ (univ.filter (fun e => st (s e) ≠ st (t e))).card =
      ∏ v, if st v then (-1 : ℝ) ^ valence s t v else 1 := by
  have fibre (f : E → V) :
      (∏ v, spinSign (st v) ^ (univ.filter (fun e => f e = v)).card) =
        ∏ e, spinSign (st (f e)) := by
    simp_rw [← Finset.prod_const]
    exact Finset.prod_fiberwise' univ f (fun v => spinSign (st v))
  calc
    _ = ∏ e, spinSign (st (s e)) * spinSign (st (t e)) := by
      rw [← Finset.prod_const, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro e he
      cases hs : st (s e) <;> cases ht : st (t e) <;> simp [spinSign, hs, ht]
    _ = (∏ v, spinSign (st v) ^ (univ.filter (fun e => s e = v)).card) *
        ∏ v, spinSign (st v) ^ (univ.filter (fun e => t e = v)).card := by
      rw [Finset.prod_mul_distrib, fibre s, fibre t]
    _ = ∏ v, if st v then (-1 : ℝ) ^ valence s t v else 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      cases h : st v <;> simp [spinSign, h, valence, pow_add]

set_option maxHeartbeats 800000 in
private theorem full_spin_sum {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (s t : E → V) (n k : E → ℕ) :
    (∑ st : V → Bool,
      C ((-1 : ℝ) ^ (univ.filter (fun e => st (s e) ≠ st (t e))).card) *
        X ^ (∑ v ∈ univ.filter (fun v => st v = true), mass s t n k v)) =
      ∏ v, (1 + C ((-1 : ℝ) ^ valence s t v) * X ^ mass s t n k v) := by
  calc
    _ = ∑ st : V → Bool, ∏ v,
        if st v then C ((-1 : ℝ) ^ valence s t v) * X ^ mass s t n k v else 1 := by
      apply Finset.sum_congr rfl
      intro st hst
      rw [sign_by_vertices, map_prod, ← Finset.prod_pow_eq_pow_sum]
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v hv
      cases h : st v <;> simp [h]
    _ = ∏ v, ∑ b : Bool,
        if b then C ((-1 : ℝ) ^ valence s t v) * X ^ mass s t n k v else 1 :=
      (Fintype.prod_sum (fun (v : V) (b : Bool) =>
        if b then C ((-1 : ℝ) ^ valence s t v) * X ^ mass s t n k v else
          (1 : Polynomial ℝ))).symm
    _ = _ := by simp [Fintype.sum_bool, add_comm]

-- Keep the spin function type abstract while checking this identity. In
-- particular, no concrete universe of 2^123 spin states is unfolded below.
private theorem treePoly_minus_one {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (s t : E → V) (n : E → ℕ)
    (rho : (E → ℕ) → ℝ) :
    treePoly s t n rho (-1) = ∑ k ∈ splits n,
      C (rho k) * ∏ v,
        (1 + C ((-1 : ℝ) ^ valence s t v) * X ^ mass s t n k v) := by
  unfold treePoly
  simp_rw [full_spin_sum]

private theorem fixed_spin_product (a b : ℕ) :
    (∏ v : Vertex,
      (1 + C ((-1 : ℝ) ^ valence src tgt v) *
        X ^ mass src tgt totals (split a b) v)) =
      (1-X)^120 * (1-X^(60+a)) * (1-X^(60+b)) * (1+X^((3-a)+(3-b))) := by
  simp [Fintype.prod_option, Fintype.prod_prod_type, Fintype.prod_bool,
    valence_centre, valence_hub, valence_leaf, mass_centre, mass_hub, mass_leaf]
  ring

private theorem physical_polynomial_raw :
    treePoly src tgt totals (physicalRho src tgt totals) (-1) =
      C physicalScalar * (1-X)^120 *
        (7442*(1-X^62)^2*(1+X^2) +
          488*(1-X^62)*(1-X^61)*(1+X^3) + 9*(1-X^61)^2*(1+X^4)) := by
  rw [treePoly_minus_one, four_splits]
  have h11 := physical_weights.1
  have h12 := physical_weights.2.1
  have h21 := physical_weights.2.2.1
  have h22 := physical_weights.2.2.2
  have hne : split 1 1 ≠ split 1 2 ∧ split 1 1 ≠ split 2 1 ∧
      split 1 1 ≠ split 2 2 ∧ split 1 2 ≠ split 2 1 ∧
      split 1 2 ≠ split 2 2 ∧ split 2 1 ≠ split 2 2 := by
    have hinj (a b c d : ℕ) (he : split a b = split c d) : a = c ∧ b = d := by
      constructor
      · simpa [split] using congrFun he (false, none)
      · simpa [split] using congrFun he (true, none)
    repeat' constructor
    all_goals
      intro he
      have hi := hinj _ _ _ _ he
      omega
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, hne, or_self, not_false_eq_true]
  rw [fixed_spin_product, fixed_spin_product, fixed_spin_product, fixed_spin_product,
    h11, h12, h21, h22]
  simp only [map_mul, map_ofNat, Nat.reduceAdd, Nat.reduceSub]
  generalize (1 - X : Polynomial ℝ)^120 = A
  generalize (1 - X^61 : Polynomial ℝ) = B
  generalize (1 - X^62 : Polynomial ℝ) = D
  ring

private theorem geom_factor (m : ℕ) : (1-X) * geom m = 1 - X^m := by
  induction m with
  | zero => simp [geom]
  | succ m ih =>
    simp only [geom, Finset.sum_range_succ] at *
    rw [mul_add, ih, pow_succ]
    ring

private theorem physical_polynomial :
    treePoly src tgt totals (physicalRho src tgt totals) (-1) =
      C physicalScalar * (1-X)^122 * obstruction := by
  rw [physical_polynomial_raw]
  have h61 := geom_factor 61
  have h62 := geom_factor 62
  rw [← h61, ← h62]
  unfold obstruction
  generalize (1 - X : Polynomial ℝ) = Y
  generalize geom 61 = B
  generalize geom 62 = D
  ring

private theorem obstruction_moments :
    obstruction.derivative.eval 1 = 62 * 60972306 ∧
    obstruction.derivative.derivative.eval 1 =
      (62^2 - 62 : ℝ) * 60972306 + 39079341096 := by
  norm_num [obstruction, geom, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_sum,
    Finset.sum_range_succ]


private theorem square_identity (h d t : ℝ) (a b K : ℂ) :
    h * (h * normSq a + 2*t*(a*conj b*K).re + d*normSq b) =
      normSq ((h : ℂ)*a + (t : ℂ)*conj K*b) +
        (h*d-t^2*normSq K)*normSq b := by
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im]
  <;> ring

private theorem cubic_positive (c : ℝ) (hc : 9/10 ≤ c) :
    0 < 2*c^3+3*c-4 := by
  have h : 0 ≤ (c-9/10)*(2*c^2+(9/5)*c+231/50) := by
    apply mul_nonneg (by linarith)
    nlinarith [sq_nonneg c]
  nlinarith

private theorem phase_identity (z u : ℂ) (hz : ‖z‖ = 1) (hu : ‖u‖ = 1) :
    7442*(1-z*u)^2*(1+z^2) +
      488*(1-z*u)*(1-u)*(1+z^3) + 9*(1-u)^2*(1+z^4) =
    -2*z^2*u *
      ((7442*z.re*normSq (1-z*u) +
        488*((1-z*u)*conj (1-u)*((z+conj z^2)/2)).re +
        9*(2*z.re^2-1)*normSq (1-u) : ℝ) : ℂ) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hzc : conj z = z⁻¹ := (Complex.inv_eq_conj hz).symm
  have huc : conj u = u⁻¹ := (Complex.inv_eq_conj hu).symm
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one,
    Complex.re_eq_add_conj, Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_mul, map_add, map_div₀, map_pow, map_one, map_ofNat,
    map_inv₀, conj_conj, hzc, huc, inv_inv]
  field_simp
  <;> ring

private theorem kernel_norm (z : ℂ) (hz : ‖z‖ = 1) :
    normSq ((z+conj z^2)/2) = (1+4*z.re^3-3*z.re)/2 := by
  have hn : z.re^2 + z.im^2 = 1 := by
    simpa [Complex.normSq, pow_two] using
      (show normSq z = 1 by rw [Complex.normSq_eq_norm_sq, hz]; norm_num)
  simp [Complex.normSq, Complex.div_re, Complex.div_im, Complex.mul_re,
    Complex.mul_im, pow_two]
  linear_combination (z.re^2+z.im^2+2-6*z.re)/4 * hn

private theorem product_moments (s : Multiset ℂ)
    (hs : ∀ r ∈ s, 1-r ≠ 0) :
    let p : Polynomial ℂ := (s.map fun r => X-C r).prod
    let v := (s.map fun r => 1/(1-r)).sum
    let w := (s.map fun r => (1/(1-r))^2).sum
    p.derivative.eval 1 = p.eval 1*v ∧
      p.derivative.derivative.eval 1 = p.eval 1*(v^2-w) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (by simp)
    have ht := ih (by intro r hr; exact hs r (by simp [hr]))
    dsimp at *
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
      derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      derivative_one, zero_mul, zero_add]
    simp only [ht.1, ht.2]
    constructor <;> field_simp <;> ring

-- The fixed certificate uses a non-strict bound, valid even for the empty
-- multiset. Its exact positive arithmetic gap supplies the contradiction.
private theorem multiset_sum_le (s : Multiset ℝ)
    (h : ∀ x ∈ s, x ≤ 5) : s.sum ≤ (s.card : ℝ)*5 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := h a (by simp)
    have ht := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    linarith

private theorem unit_inverse_moment (z : ℂ) (hz : ‖z‖ = 1)
    (hc : z.re < 9/10) :
    ((1 / (1-z)) - (1 / (1-z))^2).re < 5 := by
  have hn : normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hne : 1-z ≠ 0 := by
    intro h
    have he : z = 1 := by linear_combination -h
    simp [he] at hc
    norm_num at hc
  have hreal : 1-z.re ≠ 0 := by linarith
  have hid : (1 / (1-z)) - (1 / (1-z))^2 =
      (1 / (2*(1-z.re)) : ℝ) := by
    apply Complex.ext <;>
      simp [Complex.normSq, Complex.div_re, Complex.div_im,
        Complex.mul_re, Complex.mul_im, pow_two] at * <;>
      field_simp <;>
      first
      | nlinarith
      | linear_combination z.im * hn
  rw [hid, Complex.ofReal_re]
  apply (div_lt_iff₀ (by linarith : 0 < 2*(1-z.re))).mpr
  linarith

private theorem fixed_moment_contradiction (p : Polynomial ℂ)
    (h0 : p.eval 1 = 60972306)
    (h1 : p.derivative.eval 1 = 3780282972)
    (h2 : p.derivative.derivative.eval 1 = 269676602388)
    (hdeg : p.natDegree ≤ 124)
    (harc : ∀ r : ℂ, p.IsRoot r → ‖r‖ = 1 → r.re < 9/10) :
    ∃ r : ℂ, p.IsRoot r ∧ ‖r‖ ≠ 1 := by
  classical
  by_contra! hall
  have hp : p ≠ 0 := by intro he; simp [he] at h0
  have hnonzero : p.eval 1 ≠ 0 := by rw [h0]; norm_num
  have hs : ∀ r ∈ p.roots, 1-r ≠ 0 := by
    intro r hr he
    have hr0 := Polynomial.isRoot_of_mem_roots hr
    have her : r = 1 := by linear_combination -he
    subst r
    exact hnonzero hr0
  let v := (p.roots.map fun r => 1/(1-r)).sum
  let w := (p.roots.map fun r => (1/(1-r))^2).sum
  have hm := product_moments p.roots hs
  dsimp at hm
  have factor := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := p))
  have hfactor : p = C p.leadingCoeff * (p.roots.map fun r => X-C r).prod := factor.symm
  have hv : p.derivative.eval 1 = p.eval 1*v := by
    conv_lhs => rw [hfactor]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
    rw [hm.1]
    conv_rhs => lhs; rw [hfactor]
    simp only [eval_mul, eval_C]
    ring
  have hw : p.derivative.derivative.eval 1 = p.eval 1*(v^2-w) := by
    conv_lhs => rw [hfactor]
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C]
    rw [hm.2]
    conv_rhs => lhs; rw [hfactor]
    simp only [eval_mul, eval_C]
    ring
  have hv62 : v = 62 := by
    rw [h0, h1] at hv
    linear_combination -hv / 60972306
  have hsum : ((p.roots.map fun r => 1/(1-r)-(1/(1-r))^2).sum).re ≤ 620 := by
    change Complex.reAddGroupHom _ ≤ 620
    rw [map_multiset_sum]
    have hu := multiset_sum_le (p.roots.map fun r =>
      (1/(1-r)-(1/(1-r))^2).re) (by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
        have hz := Polynomial.isRoot_of_mem_roots hr
        exact (unit_inverse_moment r (hall r hz) (harc r hz (hall r hz))).le)
    simpa [Multiset.map_map, Function.comp_def, Complex.reAddGroupHom] using
      (hu.trans (by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree]
        have hn : (p.natDegree : ℝ) ≤ 124 := by exact_mod_cast hdeg
        calc
          (p.natDegree : ℝ)*5 ≤ 124*5 :=
            mul_le_mul_of_nonneg_right hn (by norm_num)
          _ = 620 := by norm_num))
  have hsum_eq : (p.roots.map fun r => 1/(1-r)-(1/(1-r))^2).sum = v-w := by
    exact Multiset.sum_map_sub
  rw [hsum_eq, hv62, Complex.sub_re] at hsum
  rw [h0, h2, hv62] at hw
  have hre := congrArg Complex.re hw
  norm_num [Complex.mul_re, Complex.sub_re] at hre hsum
  nlinarith

private theorem fixed_arc_exclusion (p : Polynomial ℂ)
    (hone : p.eval 1 ≠ 0)
    (hraw : ∀ z : ℂ, (1-z)^2*p.eval z =
      7442*(1-z^62)^2*(1+z^2) +
        488*(1-z^62)*(1-z^61)*(1+z^3) + 9*(1-z^61)^2*(1+z^4)) :
    ∀ z : ℂ, p.IsRoot z → ‖z‖ = 1 → z.re < 9/10 := by
  intro z hzroot hz
  by_contra! hc
  let a := 1-z^62
  let b := 1-z^61
  let K := (z+conj z^2)/2
  let h : ℝ := 7442*z.re
  let d : ℝ := 9*(2*z.re^2-1)
  let E : ℝ := h*normSq a + 488*(a*conj b*K).re + d*normSq b
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have hraw0 : 7442*a^2*(1+z^2) +
      488*a*b*(1+z^3)+9*b^2*(1+z^4) = 0 := by
    rw [← hraw, hzroot]
    simp
  have phase := phase_identity z (z^61) hz (by simp [norm_pow, hz])
  have haz : 1-z*z^61 = a := by
    dsimp [a]
    exact congrArg (fun t : ℂ => 1-t) (pow_succ' z 61).symm
  rw [haz] at phase
  have hEcast : (E : ℂ) = 0 := by
    have heq : -2*z^2*z^61*(E : ℂ) = 0 := by
      simpa only [a, b, K, h, d, E] using phase.symm.trans hraw0
    exact (mul_eq_zero.mp heq).resolve_left (by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hz0))
        (pow_ne_zero _ hz0))
  have hE : E = 0 := by exact_mod_cast hEcast
  have hh : 0 < h := by dsimp [h]; linarith
  have hdet : 0 < h*d-244^2*normSq K := by
    have hk := kernel_norm z hz
    have hp := cubic_positive z.re hc
    dsimp [h, d, K] at *
    nlinarith
  have hsq := square_identity h d 244 a b K
  have hb0 : normSq b = 0 := by
    have hn := normSq_nonneg ((h : ℂ)*a+244*conj K*b)
    have hb := normSq_nonneg b
    rw [show (2 : ℝ)*244 = 488 by norm_num] at hsq
    change h*E = _ at hsq
    rw [hE] at hsq
    norm_num only [Complex.ofReal_ofNat, mul_zero] at hsq
    nlinarith
  have hb : b = 0 := normSq_eq_zero.mp hb0
  have ha0 : normSq a = 0 := by
    dsimp [E] at hE
    simp only [hb, normSq_zero, map_zero, mul_zero, zero_mul, zero_re, add_zero] at hE
    exact (mul_eq_zero.mp hE).resolve_left (ne_of_gt hh)
  have ha : a = 0 := normSq_eq_zero.mp ha0
  have hz61 : z^61 = 1 := by dsimp [b] at hb; linear_combination -hb
  have hz62 : z^62 = 1 := by dsimp [a] at ha; linear_combination -ha
  have he : z = 1 := by
    rw [show 62=61+1 by decide, pow_succ, hz61, one_mul] at hz62
    exact hz62
  subst z
  exact hone hzroot


private theorem obstruction_raw_identity :
    (1-X)^2*obstruction =
      7442*(1-X^62)^2*(1+X^2) +
        488*(1-X^62)*(1-X^61)*(1+X^3) + 9*(1-X^61)^2*(1+X^4) := by
  rw [← geom_factor 62, ← geom_factor 61]
  unfold obstruction
  generalize (1 - X : Polynomial ℝ) = Y
  generalize geom 61 = B
  generalize geom 62 = D
  ring

private theorem obstruction_degree_le : obstruction.natDegree ≤ 124 := by
  have hg (m : ℕ) : (geom (m+1)).natDegree ≤ m := by
    unfold geom
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    rw [Polynomial.natDegree_X_pow]
    have hi := Finset.mem_range.mp hj
    omega
  have h62 : (geom 62).natDegree ≤ 61 := hg 61
  have h61 : (geom 61).natDegree ≤ 60 := hg 60
  unfold obstruction
  generalize he62 : geom 62 = g62 at h62 ⊢
  generalize he61 : geom 61 = g61 at h61 ⊢
  compute_degree <;> omega

private theorem obstruction_off_circle :
    ∃ z : ℂ, (obstruction.map (algebraMap ℝ ℂ)).IsRoot z ∧ ‖z‖ ≠ 1 := by
  let p := obstruction.map (algebraMap ℝ ℂ)
  have h0 : p.eval 1 = 60972306 := by
    dsimp only [p]
    rw [Polynomial.eval_one_map, obstruction_one]
    norm_num
  have h1 : p.derivative.eval 1 = 3780282972 := by
    dsimp only [p]
    rw [Polynomial.derivative_map, Polynomial.eval_one_map, obstruction_moments.1]
    norm_num
  have h2 : p.derivative.derivative.eval 1 = 269676602388 := by
    dsimp only [p]
    rw [Polynomial.derivative_map, Polynomial.derivative_map,
      Polynomial.eval_one_map, obstruction_moments.2]
    norm_num
  have hd : p.natDegree ≤ 124 := by
    exact (Polynomial.natDegree_map_le).trans obstruction_degree_le
  have hr : ∀ z : ℂ, (1-z)^2*p.eval z =
      7442*(1-z^62)^2*(1+z^2) +
        488*(1-z^62)*(1-z^61)*(1+z^3) + 9*(1-z^61)^2*(1+z^4) := by
    intro z
    have h := congrArg (fun q : Polynomial ℝ =>
      (q.map (algebraMap ℝ ℂ)).eval z) obstruction_raw_identity
    simpa [p] using h
  exact fixed_moment_contradiction p h0 h1 h2 hd
    (fixed_arc_exclusion p (by rw [h0]; norm_num) hr)

/- result
   proof_shape: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#17677; Refuted)
   Direct frozen source dependency:
   D5/S3/Zeros/LeeYang/QuiverTreeIsingRefutation
     statement_id: sha256:4e16a57cc1a3325fd3e59f72a2b703328902d8320368e6143e9fdcdb89de530c
   The designated literal refutation result is exempt from escape registration.
   Classification is relative to the imported public source and pinned Mathlib:
   the fixed finite construction, product and derivative inductions, norm-square
   algebra and polynomial normalization are consumed by the single refutation.
   Admission is the preregistered external open-problem settlement, not a claim
   that these standard mathematical operations supply a new generic theorem.
   The source (2.31) prints m; the registered construction uses every m+1 vertex.
   No published erratum, priority, minimality or other tau classification is claimed.
   The private theorem helpers in this module have proof_shape: bind-only,
   escape_witness: none;
   their live consumers are:
   legal_parts: four_splits.
   totals_admissible: four_splits, result.
   nonloop: tree_ok.
   edge_injective: tree_ok.
   tree_ok: result.
   split_legal: four_splits.
   four_splits: physical_polynomial_raw.
   mass_centre: vertex_centre, fixed_spin_product.
   mass_hub: vertex_hub, fixed_spin_product.
   mass_leaf: vertex_leaf, fixed_spin_product.
   valence_centre: vertex_centre, fixed_spin_product.
   valence_hub: vertex_hub, fixed_spin_product.
   valence_leaf: vertex_leaf, fixed_spin_product.
   vertex_leaf: physical_weight_expansion.
   vertex_hub: physical_weights.
   vertex_centre: physical_weights.
   physical_weight_expansion: physical_weights.
   physical_weights: physical_polynomial_raw.
   geom_one: obstruction_one.
   obstruction_one: obstruction_off_circle.
   sign_by_vertices: full_spin_sum.
   full_spin_sum: treePoly_minus_one.
   treePoly_minus_one: physical_polynomial_raw.
   fixed_spin_product: physical_polynomial_raw.
   physical_polynomial_raw: physical_polynomial.
   geom_factor: physical_polynomial, obstruction_raw_identity.
   physical_polynomial: result.
   obstruction_moments: obstruction_off_circle.
   square_identity: fixed_arc_exclusion.
   cubic_positive: fixed_arc_exclusion.
   phase_identity: fixed_arc_exclusion.
   kernel_norm: fixed_arc_exclusion.
   product_moments: fixed_moment_contradiction.
   multiset_sum_le: fixed_moment_contradiction.
   unit_inverse_moment: fixed_moment_contradiction.
   fixed_moment_contradiction: obstruction_off_circle.
   fixed_arc_exclusion: obstruction_off_circle.
   obstruction_raw_identity: obstruction_off_circle.
   obstruction_degree_le: obstruction_off_circle.
   obstruction_off_circle: result.
-/
theorem result : ¬ claimPhys := by
  intro h
  obtain ⟨z, hz, hn⟩ := obstruction_off_circle
  apply hn
  apply h Vertex Edge src tgt tree_ok (by norm_num [Edge]) totals totals_admissible z
  change ((treePoly src tgt totals (physicalRho src tgt totals) (-1)).map
    (algebraMap ℝ ℂ)).eval z = 0
  rw [physical_polynomial]
  simp only [Polynomial.map_mul, Polynomial.eval_mul]
  rw [hz]
  ring

#print axioms result

end D5.S3.Zeros.LeeYang.QuiverTreePhysicalCounterexample
