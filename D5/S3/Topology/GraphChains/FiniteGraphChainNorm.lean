/- GID: D5/S3/Topology/GraphChains/FiniteGraphChainNorm
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-sharp-four-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The bounded-cochain dual norm on finite real graph chains and its rooted cycle-space realization. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

compile_only_with_mathlib

/-! Omega original.

The bounded-cochain dual norm on finite real graph chains and its rooted cycle-space realization. -/

namespace Omega.GraphChains

open scoped BigOperators

noncomputable section

variable {I T : Type*} [Fintype I]

/-- The sum of the absolute values of the chain coordinates. -/
def mass (z : I → ℝ) : ℝ := ∑ i, |z i|

/-- Evaluate a coordinate cochain on a chain. -/
def pairing (f z : I → ℝ) : ℝ := ∑ i, f i * z i

/-- Cochains bounded on coordinates and on the given triangle chains. -/
def Admissible (triangle : T → I → ℝ) (f : I → ℝ) : Prop :=
  (∀ i, |f i| ≤ 3) ∧ ∀ t, |pairing f (triangle t)| ≤ 1

private theorem abs_pairing_le (f z : I → ℝ) (c : ℝ) (hf : ∀ i, |f i| ≤ c) :
    |pairing f z| ≤ c * mass z := by
  unfold pairing mass
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)

def values (triangle : T → I → ℝ) (z : I → ℝ) : Set ℝ :=
  {r | ∃ f, Admissible triangle f ∧ r = |pairing f z|}

theorem values_nonempty (triangle : T → I → ℝ) (z : I → ℝ) :
    (values triangle z).Nonempty := by
  refine ⟨0, 0, ⟨fun _ => by norm_num, fun _ => by simp [pairing]⟩, ?_⟩
  simp [pairing]

private theorem values_bddAbove (triangle : T → I → ℝ) (z : I → ℝ) :
    BddAbove (values triangle z) :=
  ⟨3 * mass z, by rintro _ ⟨f, hf, rfl⟩; exact abs_pairing_le f z 3 hf.1⟩

/-- The dual norm obtained from bounded cochains of triangle defect at most one. -/
def dualNorm (triangle : T → I → ℝ) (z : I → ℝ) : ℝ := sSup (values triangle z)

theorem abs_pairing_le_dualNorm {triangle : T → I → ℝ} {f : I → ℝ}
    (hf : Admissible triangle f) (z : I → ℝ) : |pairing f z| ≤ dualNorm triangle z :=
  le_csSup (values_bddAbove triangle z) ⟨f, hf, rfl⟩

theorem dualNorm_triangle (triangle : T → I → ℝ) (t : T) : dualNorm triangle (triangle t) ≤ 1 := by
  apply csSup_le (values_nonempty triangle _)
  rintro _ ⟨f, hf, rfl⟩
  exact hf.2 t

theorem dualNorm_le_mass (triangle : T → I → ℝ) (z : I → ℝ) :
    dualNorm triangle z ≤ 3 * mass z :=
  csSup_le (values_nonempty triangle z) (fun _ ⟨f, hf, hr⟩ => hr.symm ▸ abs_pairing_le f z 3 hf.1)

theorem mass_le_dualNorm {triangle : T → I → ℝ} (h : ∀ t, mass (triangle t) ≤ 3)
    (z : I → ℝ) : mass z ≤ 3 * dualNorm triangle z := by
  let f (i : I) : ℝ := if 0 ≤ z i then 1 / 3 else -(1 / 3)
  have hf (i : I) : |f i| ≤ 1 / 3 := by
    unfold f
    split <;> norm_num
  have had : Admissible triangle f := by
    refine ⟨fun i => (hf i).trans (by norm_num), fun t => ?_⟩
    exact (abs_pairing_le f (triangle t) (1 / 3) hf).trans (by linarith [h t])
  have he : pairing f z = (1 / 3) * mass z := by
    unfold pairing mass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ z i
    · simp [f, hi, abs_of_nonneg hi]
    · simp [f, hi, abs_of_neg (lt_of_not_ge hi)]
  have hh := abs_pairing_le_dualNorm had z
  have hm : 0 ≤ mass z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [he, abs_of_nonneg (by positivity)] at hh
  linarith

/-- Real coordinate chains with the norm dual to the bounded admissible cochains. -/
def DualChains (triangle : T → I → ℝ) := I → ℝ

instance (triangle : T → I → ℝ) : AddCommGroup (DualChains triangle) :=
  inferInstanceAs (AddCommGroup (I → ℝ))
instance (triangle : T → I → ℝ) : Module ℝ (DualChains triangle) :=
  inferInstanceAs (Module ℝ (I → ℝ))
instance (triangle : T → I → ℝ) : FiniteDimensional ℝ (DualChains triangle) :=
  inferInstanceAs (FiniteDimensional ℝ (I → ℝ))
instance (triangle : T → I → ℝ) : Norm (DualChains triangle) := ⟨dualNorm triangle⟩

private theorem dualNorm_smul_le (triangle : T → I → ℝ) (a : ℝ) (z : I → ℝ) :
    dualNorm triangle (a • z) ≤ |a| * dualNorm triangle z := by
  apply csSup_le (values_nonempty triangle _)
  rintro _ ⟨f, hf, rfl⟩
  have he : pairing f (a • z) = a * pairing f z := by
    simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_pairing_le_dualNorm hf z) (abs_nonneg _)

private theorem dualNorm_zero (triangle : T → I → ℝ) :
    dualNorm triangle 0 = 0 :=
  le_antisymm (by simpa [mass] using dualNorm_le_mass triangle 0)
    (by
      have h : Admissible triangle (0 : I → ℝ) := by constructor <;> simp [pairing]
      simpa [pairing] using abs_pairing_le_dualNorm h (0 : I → ℝ))

/-- Norm structure for the cochain dual when all triangle chains have mass at most three. -/
def dualChainsCore (triangle : T → I → ℝ) (h : ∀ t, mass (triangle t) ≤ 3) :
    NormedSpace.Core ℝ (DualChains triangle) where
  norm_nonneg z :=
    (abs_nonneg _).trans (abs_pairing_le_dualNorm
      (f := 0) (by constructor <;> simp [pairing]) z)
  norm_triangle x y := by
    change dualNorm triangle (x + y) ≤ dualNorm triangle x + dualNorm triangle y
    apply csSup_le (values_nonempty triangle _)
    rintro _ ⟨f, hf, rfl⟩
    have he : pairing f (x + y) = pairing f x + pairing f y := by
      unfold pairing
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change f i * ((show I → ℝ from x) i + (show I → ℝ from y) i) = _
      exact mul_add _ _ _
    rw [he]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_pairing_le_dualNorm hf x) (abs_pairing_le_dualNorm hf y))
  norm_smul a z := by
    let z' : I → ℝ := z
    change dualNorm triangle (a • z') = ‖a‖ * dualNorm triangle z'
    rw [Real.norm_eq_abs]
    refine le_antisymm (dualNorm_smul_le triangle a z') ?_
    by_cases ha : a = 0
    · simp [ha, dualNorm_zero]
    have hi := dualNorm_smul_le triangle a⁻¹ (a • z')
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul, abs_inv, ← div_eq_inv_mul,
      le_div_iff₀ (abs_pos.mpr ha), mul_comm] at hi
    exact hi
  norm_eq_zero_iff z := by
    change dualNorm triangle z = 0 ↔ z = 0
    refine ⟨fun hz => ?_, fun hz => hz ▸ dualNorm_zero triangle⟩
    funext i
    have hm := mass_le_dualNorm h (show I → ℝ from z)
    rw [hz, mul_zero] at hm
    exact abs_nonpos_iff.mp
      ((Finset.single_le_sum (f := fun j => |z j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)).trans hm)

section GraphChains

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Directed coordinates for real edge chains. Each oriented edge has two opposite entries. -/
abbrev Chains (V : Type*) := (V × V) → ℝ

/-- The oriented edge chain, zero when its endpoints coincide. -/
def orientedEdge (u v : V) : Chains V :=
  (1 / 2 : ℝ) • (Pi.single (u, v) 1 - Pi.single (v, u) 1)

theorem orientedEdge_reverse (u v : V) : orientedEdge v u = -orientedEdge u v := by
  unfold orientedEdge
  rw [← smul_neg, neg_sub]

theorem mass_add (c d : Chains V) : mass (c + d) ≤ mass c + mass d := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (c i) (d i)

theorem mass_neg (c : Chains V) : mass (-c) = mass c := by
  simp [mass]

private theorem mass_single (e : V × V) (a : ℝ) : mass (Pi.single e a) = |a| := by
  simp [mass, Pi.single_apply, apply_ite abs]

private theorem mass_smul (a : ℝ) (c : Chains V) : mass (a • c) = |a| * mass c := by
  simp [mass, abs_mul, Finset.mul_sum]

theorem mass_orientedEdge_le (u v : V) : mass (orientedEdge u v) ≤ 1 := by
  rw [orientedEdge, mass_smul, sub_eq_add_neg]
  have h := mass_add (Pi.single (u, v) (1 : ℝ)) (-Pi.single (v, u) (1 : ℝ))
  simp [mass_neg, mass_single] at h
  norm_num
  linarith

/-- The boundary reads net incoming mass in each directed coordinate. -/
def boundary (c : Chains V) : V → ℝ := fun v => ∑ u, (c (u, v) - c (v, u))

private theorem boundary_add (c d : Chains V) : boundary (c + d) = boundary c + boundary d := by
  ext v
  simp only [boundary, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

private theorem boundary_smul (r : ℝ) (c : Chains V) :
    boundary (r • c) = r • boundary c := by
  ext v
  simp [boundary, mul_sub, Finset.mul_sum]

theorem boundary_sub (c d : Chains V) : boundary (c - d) = boundary c - boundary d := by
  have h := boundary_smul (-1) d
  simp only [neg_smul, one_smul] at h
  simp only [sub_eq_add_neg, boundary_add, h]

theorem boundary_orientedEdge (u v : V) :
    boundary (orientedEdge u v) = Pi.single v 1 - Pi.single u 1 := by
  ext x
  simp only [boundary, orientedEdge, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  have first (a b : V) : (∑ y : V, (Pi.single (M := fun _ : V × V => ℝ) (a, b) 1) (y, x)) =
      Pi.single (M := fun _ : V => ℝ) b 1 x := by
    by_cases h : x = b <;> simp [Pi.single_apply, Prod.mk.injEq, h]
  have second (a b : V) : (∑ y : V, (Pi.single (M := fun _ : V × V => ℝ) (a, b) 1) (x, y)) =
      Pi.single (M := fun _ : V => ℝ) a 1 x := by
    by_cases h : x = a <;> simp [Pi.single_apply, Prod.mk.injEq, h]
  rw [first, first, second, second]
  ring

/-- Edge support as a linear constraint. -/
def Supported (G : SimpleGraph V) (c : Chains V) : Prop :=
  ∀ uv : V × V, ¬G.Adj uv.1 uv.2 → c uv = 0

private theorem supported_edge {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    Supported G (orientedEdge u v) := by
  intro uv hno
  have h₁ : uv ≠ (u, v) := by rintro rfl; exact hno h
  have h₂ : uv ≠ (v, u) := by rintro rfl; exact hno h.symm
  simp [orientedEdge, Pi.single_apply, h₁, h₂]

private theorem Supported.add {G : SimpleGraph V} {c d : Chains V}
    (hc : Supported G c) (hd : Supported G d) : Supported G (c + d) := by
  intro uv huv
  simp [hc uv huv, hd uv huv]

private theorem Supported.sub {G : SimpleGraph V} {c d : Chains V}
    (hc : Supported G c) (hd : Supported G d) : Supported G (c - d) := by
  intro uv huv
  simp [hc uv huv, hd uv huv]

/-- The three ordered vertices of a triangle of a simple graph. -/
abbrev Triangles (G : SimpleGraph V) :=
  {t : V × V × V // G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.1 t.2.2}

/-- The oriented boundary of a triangle. -/
def triangleChain {G : SimpleGraph V} (t : Triangles G) : Chains V :=
  orientedEdge t.1.1 t.1.2.1 + orientedEdge t.1.2.1 t.1.2.2 -
    orientedEdge t.1.1 t.1.2.2

theorem triangleChain_mass {G : SimpleGraph V} (t : Triangles G) :
    mass (triangleChain t) ≤ 3 := by
  rw [triangleChain, sub_eq_add_neg]
  have h₁ := mass_add (orientedEdge t.1.1 t.1.2.1) (orientedEdge t.1.2.1 t.1.2.2)
  have h₂ := mass_add
    (orientedEdge t.1.1 t.1.2.1 + orientedEdge t.1.2.1 t.1.2.2)
    (-orientedEdge t.1.1 t.1.2.2)
  rw [mass_neg] at h₂
  linarith [mass_orientedEdge_le t.1.1 t.1.2.1, mass_orientedEdge_le t.1.2.1 t.1.2.2,
    mass_orientedEdge_le t.1.1 t.1.2.2]

private abbrev ChainsWithNorm (G : SimpleGraph V) := DualChains (triangleChain (G := G))
private instance (G : SimpleGraph V) : NormedAddCommGroup (ChainsWithNorm G) :=
  .ofCore (dualChainsCore _ triangleChain_mass)
private instance (G : SimpleGraph V) : NormedSpace ℝ (ChainsWithNorm G) :=
  .ofCore (dualChainsCore _ triangleChain_mass)

/-- Cycles are the supported chains of zero boundary. -/
private def cycleSubmodule (G : SimpleGraph V) : Submodule ℝ (ChainsWithNorm G) where
  carrier := {c | Supported G c ∧ boundary c = 0}
  zero_mem' := ⟨fun _ _ => rfl, by change boundary (0 : Chains V) = 0; ext v; simp [boundary]⟩
  add_mem' := by
    rintro c d ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨hc.add hd, ?_⟩
    change boundary ((show Chains V from c) + (show Chains V from d)) = 0
    rw [boundary_add, hc', hd', add_zero]
  smul_mem' := by
    rintro r c ⟨hc, hc'⟩
    refine ⟨fun uv huv => ?_, ?_⟩
    · change r * (show Chains V from c) uv = 0
      rw [hc uv huv, mul_zero]
    · change boundary (r • (show Chains V from c)) = 0
      rw [boundary_smul, hc', smul_zero]

private def walkChain {G : SimpleGraph V} {u v : V} : G.Walk u v → Chains V
  | .nil => 0
  | @SimpleGraph.Walk.cons _ _ _ x _ h p => orientedEdge u x + walkChain p

private theorem walkChain_spec {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Supported G (walkChain p) ∧ boundary (walkChain p) = Pi.single v 1 - Pi.single u 1 := by
  induction p with
  | nil => exact ⟨fun _ _ => rfl, by ext x; simp [walkChain, boundary]⟩
  | cons h p ih =>
    refine ⟨(supported_edge h).add ih.1, ?_⟩
    rw [walkChain, boundary_add, boundary_orientedEdge, ih.2]
    abel

/-- Realize a rooted chain obstruction by a finite-dimensional Banach-valued gain. -/
theorem gain_of_rooted_chain_obstruction (G : SimpleGraph V) (hc : G.Connected) (o : V) (R : ℝ)
    (obstruction : ∀ p : V → Chains V, (∀ v, Supported G (p v)) →
      (∀ v, boundary (p v) = Pi.single v 1 - Pi.single o 1) →
      ∃ u v, G.Adj u v ∧ R ≤
        dualNorm (triangleChain (G := G)) (orientedEdge u v + p u - p v)) :
    ∃ (E : Type u) (N : NormedAddCommGroup E) (S : @NormedSpace ℝ E _ N.toSeminormedAddCommGroup),
      letI := N
      letI := S
      ∃ (_ : CompleteSpace E) (_ : FiniteDimensional ℝ E) (g : V → V → E),
        (∀ u v, g v u = -g u v) ∧
        (∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w → ‖g u v + g v w - g u w‖ ≤ 1) ∧
        ∀ φ : V → E, ∃ u v, G.Adj u v ∧ R ≤ ‖g u v - (φ v - φ u)‖ := by
  classical
  let P (v : V) : Chains V := walkChain (hc.preconnected o v).some
  have hP (v : V) := walkChain_spec (hc.preconnected o v).some
  let C := cycleSubmodule G
  let q (u v : V) (huv : G.Adj u v) : C :=
    ⟨orientedEdge u v + P u - P v, (supported_edge huv |>.add (hP u).1).sub (hP v).1, by
      rw [boundary_sub, boundary_add, boundary_orientedEdge, (hP u).2, (hP v).2]
      abel⟩
  let g (u v : V) : C := if h : G.Adj u v then q u v h else 0
  have hg (u v : V) (h : G.Adj u v) : (show Chains V from (g u v).val) = orientedEdge u v + P u - P v := by
    simp [g, h, q]
  refine ⟨C, inferInstance, inferInstance, FiniteDimensional.complete ℝ C, inferInstance,
    g, ?_, ?_, ?_⟩
  · intro u v
    by_cases h : G.Adj u v
    · apply Subtype.ext
      change (show Chains V from (g v u).val) = -(show Chains V from (g u v).val)
      rw [hg u v h, hg v u h.symm, orientedEdge_reverse]
      abel
    · have h' : ¬G.Adj v u := fun h' => h h'.symm
      simp [g, h, h']
  · intro u v w huv hvw huw
    change dualNorm (triangleChain (G := G))
      ((show Chains V from (g u v).val) + (show Chains V from (g v w).val) -
        (show Chains V from (g u w).val)) ≤ 1
    rw [hg u v huv, hg v w hvw, hg u w huw]
    let t : Triangles G := ⟨(u, v, w), huv, hvw, huw⟩
    convert dualNorm_triangle (triangleChain (G := G)) t using 1
    unfold triangleChain t
    abel
  · intro φ
    let p (v : V) : Chains V := P v + (show Chains V from (φ v).val)
    have hφ (v : V) : Supported G (φ v).val ∧ boundary (φ v).val = 0 := (φ v).property
    obtain ⟨u, v, huv, h⟩ := obstruction p
      (fun v => (hP v).1.add (hφ v).1)
      (fun v => by
        change boundary (P v + (show Chains V from (φ v).val)) = _
        rw [boundary_add, (hP v).2, (hφ v).2, add_zero])
    refine ⟨u, v, huv, ?_⟩
    change R ≤ dualNorm (triangleChain (G := G))
      ((show Chains V from (g u v).val) - ((show Chains V from (φ v).val) - (show Chains V from (φ u).val)))
    rw [hg u v huv]
    convert h using 1
    unfold p
    abel

end GraphChains

section Pushforward

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

/-- Push a chain along a vertex map by summing over the fibers of its ordered pairs. -/
def pushChain (ρ : X → Y) (c : Chains X) : Chains Y :=
  ∑ e : X × X, Pi.single (ρ e.1, ρ e.2) (c e)

/-- Pull a cochain back by evaluating it at the image of each ordered pair. -/
def pullCochain (ρ : X → Y) (f : Chains Y) : Chains X :=
  fun e => f (ρ e.1, ρ e.2)

private theorem pairing_single (f : Chains Y) (e : Y × Y) (a : ℝ) :
    pairing f (Pi.single e a) = f e * a := by
  classical
  simp [pairing, Pi.single_apply, mul_ite]

theorem pairing_pushChain (ρ : X → Y) (c : Chains X) (f : Chains Y) :
    pairing f (pushChain ρ c) = pairing (pullCochain ρ f) c := by
  classical
  unfold pushChain
  calc
    _ = ∑ e : X × X, pairing f (Pi.single (ρ e.1, ρ e.2) (c e)) := by
      unfold pairing
      simp only [Finset.sum_apply, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ e : X × X, f (ρ e.1, ρ e.2) * c e := by simp only [pairing_single]
    _ = _ := rfl

theorem mass_pushChain (ρ : X → Y) (c : Chains X) :
    mass (pushChain ρ c) ≤ mass c := by
  classical
  unfold mass pushChain
  simp only [Finset.sum_apply]
  refine (Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  exact (mass_single _ _).le

theorem pairing_orientedEdge [DecidableEq X] (f : Chains X) (u v : X)
    (hf : ∀ u v, f (v, u) = -f (u, v)) :
    pairing f (orientedEdge u v) = f (u, v) := by
  classical
  unfold orientedEdge
  calc
    _ = (1 / 2 : ℝ) * (pairing f (Pi.single (u, v) 1) - pairing f (Pi.single (v, u) 1)) := by
      simp only [pairing, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.mul_sum, mul_sub,
        Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ = _ := by rw [pairing_single, pairing_single, hf u v]; ring

theorem pairing_triangle [DecidableEq X] (f : Chains X)
    (hf : ∀ u v, f (v, u) = -f (u, v)) (u v w : X) :
    pairing f (orientedEdge u v + orientedEdge v w - orientedEdge u w) =
      f (u, v) + f (v, w) - f (u, w) := by
  rw [← pairing_orientedEdge f u v hf, ← pairing_orientedEdge f v w hf,
    ← pairing_orientedEdge f u w hf]
  simp [pairing, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Every oriented triangle reads the alternating part of a coordinate cochain. -/
theorem pairing_triangle_alternating [DecidableEq X] (f : Chains X) (u v w : X) :
    pairing f (orientedEdge u v + orientedEdge v w - orientedEdge u w) =
      ((f (u,v) - f (v,u)) + (f (v,w) - f (w,v)) -
        (f (u,w) - f (w,u))) / 2 := by
  have h (a b : X) :
      pairing f (orientedEdge a b) = (f (a,b) - f (b,a)) / 2 := by
    unfold orientedEdge
    calc
      _ = (1 / 2 : ℝ) * (pairing f (Pi.single (a,b) 1) - pairing f (Pi.single (b,a) 1)) := by
        simp [pairing, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Finset.mul_sum, mul_sub,
          Finset.sum_sub_distrib, mul_left_comm]
      _ = _ := by rw [pairing_single, pairing_single]; ring
  have hlin :
      pairing f (orientedEdge u v + orientedEdge v w - orientedEdge u w) =
      pairing f (orientedEdge u v) + pairing f (orientedEdge v w) -
        pairing f (orientedEdge u w) := by
    simp [pairing, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub,
      Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hlin, h, h, h]
  ring

theorem dualNorm_pushChain_le [DecidableEq X] {G : SimpleGraph X} {H : SimpleGraph Y}
    (ρ : X → Y) (hρ : ∀ u v, G.Adj u v → ρ u = ρ v ∨ H.Adj (ρ u) (ρ v))
    (z : Chains X) :
    dualNorm (triangleChain (G := H)) (pushChain ρ z) ≤ dualNorm (triangleChain (G := G)) z := by
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  rw [pairing_pushChain]
  apply abs_pairing_le_dualNorm
  refine ⟨fun e => hf.1 _, fun ⟨⟨u,v,w⟩, huv, hvw, huw⟩ => ?_⟩
  change |pairing (pullCochain ρ f)
    (orientedEdge u v + orientedEdge v w - orientedEdge u w)| ≤ 1
  simp only [pairing_triangle_alternating, pullCochain]
  rcases hρ _ _ huv with h | ha
  · simp [h]
  rcases hρ _ _ hvw with h | hb
  · simp [h]
  rcases hρ _ _ huw with h | hc
  · rw [h, sub_self, sub_zero, show f (ρ w, ρ v) - f (ρ v, ρ w) +
      (f (ρ v, ρ w) - f (ρ w, ρ v)) = 0 by ring]
    norm_num
  let t : Triangles H := ⟨(ρ u, ρ v, ρ w), ha, hb, hc⟩
  have ht := hf.2 t
  change |pairing f (orientedEdge (ρ u) (ρ v) + orientedEdge (ρ v) (ρ w) -
    orientedEdge (ρ u) (ρ w))| ≤ 1 at ht
  simpa only [pairing_triangle_alternating] using ht

end Pushforward

end

end Omega.GraphChains
