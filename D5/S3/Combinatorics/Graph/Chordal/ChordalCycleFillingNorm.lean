/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalCycleFillingNorm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/ChordalCycleFillingNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded triangle-flat cochains define a finite-dimensional norm on chains. -/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph.ChordalReconstruction

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

private def values (triangle : T → I → ℝ) (z : I → ℝ) : Set ℝ :=
  {r | ∃ f, Admissible triangle f ∧ r = |pairing f z|}

private theorem values_nonempty (triangle : T → I → ℝ) (z : I → ℝ) :
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

end

noncomputable section

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

private theorem mass_add (c d : Chains V) : mass (c + d) ≤ mass c + mass d := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_add_le (c i) (d i)

private theorem mass_neg (c : Chains V) : mass (-c) = mass c := by
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

private theorem boundary_sub (c d : Chains V) : boundary (c - d) = boundary c - boundary d := by
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

theorem pullCochain_admissible [DecidableEq X] {G : SimpleGraph X} {H : SimpleGraph Y}
    (ρ : X → Y) (hρ : ∀ u v, G.Adj u v → ρ u = ρ v ∨ H.Adj (ρ u) (ρ v))
    (f : Chains Y) (hf : ∀ u v, f (v, u) = -f (u, v))
    (ha : Admissible (triangleChain (G := H)) f) :
    Admissible (triangleChain (G := G)) (pullCochain ρ f) := by
  have skew (u v : X) : pullCochain ρ f (v, u) = -pullCochain ρ f (u, v) :=
    hf (ρ u) (ρ v)
  refine ⟨fun e => ha.1 _, fun ⟨⟨u,v,w⟩, huv,hvw,huw⟩ => ?_⟩
  change |pairing (pullCochain ρ f)
    (orientedEdge u v + orientedEdge v w - orientedEdge u w)| ≤ 1
  simp only [pairing_triangle (pullCochain ρ f) skew]
  change |f (ρ u, ρ v) + f (ρ v, ρ w) - f (ρ u, ρ w)| ≤ 1
  have hdiag (x : Y) : f (x,x) = 0 := by linarith [hf x x]
  rcases hρ _ _ huv with h | h₁
  · simp [h, hdiag]
  rcases hρ _ _ hvw with h | h₂
  · simp [h, hdiag]
  rcases hρ _ _ huw with h | h₃
  · simp [h, hdiag, hf (ρ w) (ρ v)]
  let t : Triangles H := ⟨(ρ u, ρ v, ρ w), h₁, h₂, h₃⟩
  have ht := ha.2 t
  change |pairing f (orientedEdge (ρ u) (ρ v) + orientedEdge (ρ v) (ρ w) -
    orientedEdge (ρ u) (ρ w))| ≤ 1 at ht
  simpa only [pairing_triangle f hf] using ht

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

section EdgeLoads

variable {V : Type*} [Fintype V]

/-- The mass of the directed coordinates with an endpoint at a vertex, counted by incidences. -/
def load (c : Chains V) (v : V) : ℝ := ∑ u, (|c (v, u)| + |c (u, v)|)

theorem load_nonneg (c : Chains V) (v : V) : 0 ≤ load c v :=
  Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem sum_load (c : Chains V) : ∑ v, load c v = 2 * mass c := by
  unfold load mass
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib]
  nth_rw 2 [Finset.sum_comm]
  ring

theorem pairing_sub (a b c : Chains V) : pairing (a - b) c = pairing a c - pairing b c := by
  simp [pairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem pairing_chain_sub (f c d : Chains V) : pairing f (c - d) = pairing f c - pairing f d := by
  simp [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pairing_chain_add (f c d : Chains V) : pairing f (c + d) = pairing f c + pairing f d := by
  simp [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Changing bounded cochain values only on pairs meeting a set costs at most their
incident chain mass times the pointwise change bound. -/
theorem abs_pairing_change_le (a b c : Chains V) (S : Finset V) (d : ℝ) (hd : 0 ≤ d)
    (close : ∀ e, |a e - b e| ≤ d)
    (fixed : ∀ x y, x ∉ S → y ∉ S → a (x,y) = b (x,y)) :
    |pairing a c - pairing b c| ≤ d * ∑ v ∈ S, load c v := by
  classical
  rw [← pairing_sub]
  unfold pairing
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h (e : V × V) : |(a - b) e * c e| ≤
      d * ((if e.1 ∈ S then |c e| else 0) + (if e.2 ∈ S then |c e| else 0)) := by
    rw [abs_mul]
    change |a e - b e| * |c e| ≤ _
    by_cases hx : e.1 ∈ S <;> by_cases hy : e.2 ∈ S
    · simp only [hx, hy, ite_true]
      exact (mul_le_mul_of_nonneg_right (close e) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hd)
    · simpa [hx, hy] using mul_le_mul_of_nonneg_right (close e) (abs_nonneg (c e))
    · simpa [hx, hy] using mul_le_mul_of_nonneg_right (close e) (abs_nonneg (c e))
    · rw [show a e = b e from fixed e.1 e.2 hx hy]
      simp [hx, hy]
  refine (Finset.sum_le_sum fun e _ => h e).trans_eq ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [load, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · have hS : (Finset.univ.filter fun v => v ∈ S) = S := by ext; simp
    conv_rhs => rw [← hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ S <;> simp [hv]
  · rw [Finset.sum_comm]
    have hS : (Finset.univ.filter fun v => v ∈ S) = S := by ext; simp
    conv_rhs => rw [← hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ S <;> simp [hv]

/-- Incident evaluation when the cochain is a fixed scalar on edges pointing into one vertex. -/
theorem pairing_incident [DecidableEq V] (c : Chains V) (v : V) (a : ℝ) :
    pairing (fun e => a * ((if e.2 = v then 1 else 0) - (if e.1 = v then 1 else 0))) c =
      a * boundary c v := by
  classical
  unfold pairing boundary
  simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h₁ : ∑ e : V × V, (if e.2 = v then 1 else 0) * c e = ∑ u, c (u,v) := by
    rw [Fintype.sum_prod_type]
    simp [ite_mul]
  have h₂ : ∑ e : V × V, (if e.1 = v then 1 else 0) * c e = ∑ u, c (v,u) := by
    rw [Fintype.sum_prod_type]
    simp [ite_mul]
  rw [h₁, h₂, mul_sub]

end EdgeLoads

section ChainTransport

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

theorem pushChain_add (ρ : X → Y) (c d : Chains X) :
    pushChain ρ (c + d) = pushChain ρ c + pushChain ρ d := by
  ext e
  simp [pushChain, Pi.single_apply, ite_add_zero, ← Finset.sum_add_distrib]

theorem pushChain_sub (ρ : X → Y) (c d : Chains X) :
    pushChain ρ (c - d) = pushChain ρ c - pushChain ρ d := by
  ext e
  simp [pushChain, Pi.single_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f _
  split <;> simp_all

theorem pushChain_edge [DecidableEq X] (ρ : X → Y) (u v : X) :
    pushChain ρ (orientedEdge u v) = orientedEdge (ρ u) (ρ v) := by
  ext e
  simp only [pushChain, orientedEdge, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  simp only [Pi.single_apply, mul_sub, ← Finset.sum_sub_distrib]
  let a (f : X × X) : ℝ := if e = (ρ f.1, ρ f.2) then 1 / 2 else 0
  have h (b : X × X) :
      ∑ f : X × X, (if e = (ρ f.1, ρ f.2) then (1 / 2 : ℝ) * (if f = b then 1 else 0) else 0) = a b := by
    trans ∑ f : X × X, if f = b then a f else 0
    · apply Finset.sum_congr rfl
      intro f _
      by_cases hf : f = b <;> by_cases he : e = (ρ f.1, ρ f.2) <;> simp [a, hf, he]
    · simp
  rw [show (∑ i : X × X, (if e = (ρ i.1, ρ i.2) then
      (1 / 2 : ℝ) * (if i = (u,v) then 1 else 0) -
      (1 / 2 : ℝ) * (if i = (v,u) then 1 else 0) else 0)) =
    a (u,v) - a (v,u) from by
      rw [← h, ← h, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro f _
      split <;> simp_all]
  simp [a, mul_sub, mul_ite]

theorem pushChain_boundary (ρ : X → Y) (c : Chains X) (y : Y) :
    boundary (pushChain ρ c) y = ∑ x, if ρ x = y then boundary c x else 0 := by
  conv_lhs => rw [← one_mul (boundary _ _), ← pairing_incident]
  rw [pairing_pushChain]
  simp only [pairing, pullCochain, one_mul, sub_mul, Finset.sum_sub_distrib, boundary]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  simp [ite_mul, Finset.sum_ite_irrel, Finset.sum_sub_distrib, mul_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all

theorem pushChain_zero_of_not_range (ρ : X → Y) (c : Chains X) (e : Y × Y)
    (h : e.1 ∉ Set.range ρ ∨ e.2 ∉ Set.range ρ) : pushChain ρ c e = 0 := by
  simp only [pushChain, Finset.sum_apply, Pi.single_apply]
  apply Finset.sum_eq_zero
  intro f _
  refine ite_eq_right fun he => ?_
  exact h.elim (fun hn => hn ⟨f.1, (congrArg Prod.fst he).symm⟩)
    (fun hn => hn ⟨f.2, (congrArg Prod.snd he).symm⟩)

end ChainTransport

section Symmetrization

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (depth : V → ℕ) (pre : V → V → Prop)

/-- Graph automorphisms preserving the depth of each vertex. -/
def depthAutomorphisms : Subgroup (Equiv.Perm V) where
  carrier := {σ | (∀ u v, G.Adj (σ u) (σ v) ↔ G.Adj u v) ∧ (∀ v, depth (σ v) = depth v) ∧
    ∀ u v, pre (σ u) (σ v) ↔ pre u v}
  one_mem' := ⟨fun _ _ => Iff.rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, dσ, pσ⟩ ⟨hτ, dτ, pτ⟩
    exact ⟨fun u v => (hσ (τ u) (τ v)).trans (hτ u v), fun u => (dσ _).trans (dτ u),
      fun u v => (pσ (τ u) (τ v)).trans (pτ u v)⟩
  inv_mem' := by
    rintro σ ⟨hσ,dσ,pσ⟩
    exact ⟨fun u v => by simpa using (hσ (σ.symm u) (σ.symm v)).symm,
      fun u => by simpa using (dσ (σ.symm u)).symm,
      fun u v => by simpa using (pσ (σ.symm u) (σ.symm v)).symm⟩

private noncomputable instance : Fintype (depthAutomorphisms G depth pre) := Fintype.ofFinite _

/-- Average the pullbacks of a vertex-indexed chain family by depth-preserving all automorphisms. -/
noncomputable def symmetrize (p : V → Chains V) (v : V) : Chains V :=
  fun e => (Fintype.card (depthAutomorphisms G depth pre) : ℝ)⁻¹ *
    ∑ σ : depthAutomorphisms G depth pre, p (σ.val v) (σ.val e.1, σ.val e.2)

theorem symmetrize_equivariant (p : V → Chains V) (σ : depthAutomorphisms G depth pre)
    (v a b : V) :
    symmetrize G depth pre p (σ.val v) (σ.val a, σ.val b) = symmetrize G depth pre p v (a, b) := by
  unfold symmetrize
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ)
    (fun τ : depthAutomorphisms G depth pre => p (τ.val v) (τ.val a, τ.val b))

theorem symmetrize_supported (p : V → Chains V) (hp : ∀ v, Supported G (p v)) (v : V) :
    Supported G (symmetrize G depth pre p v) := by
  intro e he
  unfold symmetrize
  have h (σ : depthAutomorphisms G depth pre) :
      p (σ.val v) (σ.val e.1, σ.val e.2) = 0 :=
    hp _ _ (fun he' => he ((σ.property.1 _ _).mp he'))
  simp [h]

theorem symmetrize_boundary [DecidableEq V] (p : V → Chains V) (μ : V → ℝ)
    (hp : ∀ v, boundary (p v) = Pi.single v 1 - μ)
    (hμ : ∀ (σ : depthAutomorphisms G depth pre) (x : V), μ (σ.val x) = μ x) (v : V) :
    boundary (symmetrize G depth pre p v) = Pi.single v 1 - μ := by
  funext x
  have h (σ : depthAutomorphisms G depth pre) :
      ∑ u, (p (σ.val v) (σ.val u, σ.val x) - p (σ.val v) (σ.val x, σ.val u)) =
        (Pi.single (M := fun _ : V => ℝ) v 1 - μ) x := by
    rw [Equiv.sum_comp σ.val fun u =>
      p (σ.val v) (u, σ.val x) - p (σ.val v) (σ.val x, u)]
    change boundary (p (σ.val v)) (σ.val x) = _
    rw [hp]
    simp [Pi.single_apply, hμ, σ.val.injective.eq_iff]
  simp only [boundary, symmetrize, ← mul_sub, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have hcard : (Fintype.card (depthAutomorphisms G depth pre) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  simp [h, hcard, mul_sub, ← mul_assoc]

theorem symmetrize_mass_le (p : V → Chains V) (Λ : ℝ)
    (hp : ∀ v, mass (p v) ≤ Λ) (v : V) : mass (symmetrize G depth pre p v) ≤ Λ := by
  let L := (Fintype.card (depthAutomorphisms G depth pre) : ℝ)
  have hL : 0 < L := Nat.cast_pos.mpr Fintype.card_pos
  have hL' : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
  unfold mass symmetrize
  change (∑ e : V × V, |L⁻¹ * ∑ σ : depthAutomorphisms G depth pre,
    p (σ.val v) (σ.val e.1, σ.val e.2)|) ≤ Λ
  simp only [abs_mul, abs_of_pos (inv_pos.mpr hL), ← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun e _ => Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hL.le)).trans
  rw [Finset.sum_comm]
  have h (σ : depthAutomorphisms G depth pre) :
      ∑ e : V × V, |p (σ.val v) (σ.val e.1, σ.val e.2)| ≤ Λ :=
    (Equiv.sum_comp (σ.val.prodCongr σ.val) (fun e => |p (σ.val v) e|)).le.trans (hp _)
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h σ)
    (inv_nonneg.mpr hL.le)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change L⁻¹ * (L * Λ) ≤ Λ
  rw [← mul_assoc, hL', one_mul]

end Symmetrization

section Averages

variable {V : Type*} [Fintype V]

/-- The coordinatewise mean of a finite nonempty family of chains. -/
noncomputable def meanChain {I : Type*} [Fintype I] (c : I → Chains V) : Chains V :=
  fun e => (Fintype.card I : ℝ)⁻¹ * ∑ i, c i e

theorem pairing_mean {I : Type*} [Fintype I] (f : Chains V) (c : I → Chains V) :
    pairing f (meanChain c) = (Fintype.card I : ℝ)⁻¹ * ∑ i, pairing f (c i) := by
  unfold pairing meanChain
  simp only [mul_left_comm _ ((Fintype.card I : ℝ)⁻¹), ← Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)

theorem dualNorm_mean_le {I : Type*} [Fintype I] [Nonempty I] {T : Type*}
    (t : T → Chains V) (c : I → Chains V) (R : ℝ) (h : ∀ i, dualNorm t (c i) ≤ R) :
    dualNorm t (meanChain c) ≤ R := by
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  let N : ℝ := Fintype.card I
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  rw [pairing_mean, abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le)]
  change N⁻¹ * |∑ i, pairing f (c i)| ≤ R
  have hsum : |∑ i, pairing f (c i)| ≤ N * R :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (by
        have h' := Finset.sum_le_sum (s := (Finset.univ : Finset I))
          (fun i _ => (abs_pairing_le_dualNorm hf (c i)).trans (h i))
        simpa [N] using h')
  calc
    _ ≤ N⁻¹ * (N * R) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN.le)
    _ = R := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]

theorem pushChain_equiv [DecidableEq V] (σ : Equiv.Perm V) (c : Chains V) :
    pushChain σ.symm c = fun e => c (σ e.1, σ e.2) := by
  classical
  ext e
  unfold pushChain
  simp only [Finset.sum_apply, Pi.single_apply]
  rw [← Equiv.sum_comp (σ.prodCongr σ) (fun x : V × V =>
    if e = (σ.symm x.1, σ.symm x.2) then c x else 0)]
  cases e
  simp [Equiv.prodCongr_apply]

theorem symmetrize_residual_le [DecidableEq V] (G : SimpleGraph V) (depth : V → ℕ)
    (pre : V → V → Prop)
    (p : V → Chains V) (R : ℝ)
    (h : ∀ u v, G.Adj u v →
      dualNorm (triangleChain (G := G)) (orientedEdge u v + p u - p v) ≤ R)
    (u v : V) (huv : G.Adj u v) :
    dualNorm (triangleChain (G := G))
      (orientedEdge u v + symmetrize G depth pre p u - symmetrize G depth pre p v) ≤ R := by
  let A := depthAutomorphisms G depth pre
  let c (σ : A) := pushChain σ.val.symm (orientedEdge (σ.val u) (σ.val v) + p (σ.val u) - p (σ.val v))
  have hx : orientedEdge u v + symmetrize G depth pre p u - symmetrize G depth pre p v = meanChain c := by
    funext e
    have hc (σ : A) :
        c σ e = orientedEdge u v e + p (σ.val u) (σ.val e.1, σ.val e.2) -
          p (σ.val v) (σ.val e.1, σ.val e.2) := by
      unfold c
      rw [pushChain_sub, pushChain_add, pushChain_edge, σ.val.symm_apply_apply,
        σ.val.symm_apply_apply, pushChain_equiv, pushChain_equiv]
      rfl
    have n0 : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Pi.add_apply, Pi.sub_apply, meanChain, hc, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, symmetrize, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change _ = (Fintype.card A : ℝ)⁻¹ * _
    simp [mul_sub, mul_add, ← mul_assoc, n0, A]
  rw [hx]
  apply dualNorm_mean_le
  intro σ
  have hσ (a b : V) (hab : G.Adj a b) : σ.val.symm a = σ.val.symm b ∨
      G.Adj (σ.val.symm a) (σ.val.symm b) := by
    right
    apply (σ.property.1 _ _).mp
    simpa using hab
  exact (dualNorm_pushChain_le σ.val.symm hσ _).trans
    (h _ _ ((σ.property.1 _ _).mpr huv))

end Averages

section Normalization

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mass_sub_le (c d : Chains V) : mass (c - d) ≤ mass c + mass d := by
  rw [sub_eq_add_neg]
  simpa only [mass_neg] using mass_add c (-d)

theorem mass_mean_le {I : Type*} [Fintype I] [Nonempty I]
    (c : I → Chains V) (L : ℝ) (h : ∀ i, mass (c i) ≤ L) :
    mass (meanChain c) ≤ L := by
  let N : ℝ := Fintype.card I
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  unfold mass meanChain
  change (∑ e : V × V, |N⁻¹ * ∑ i : I, c i e|) ≤ L
  simp only [abs_mul, abs_of_nonneg (inv_nonneg.mpr hN.le), ← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr hN.le)).trans ?_
  rw [Finset.sum_comm]
  have ha : ∑ i, mass (c i) ≤ N * L := by
    have h' := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => h i)
    simpa [N] using h'
  exact (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hN.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul])

theorem boundary_mean {I : Type*} [Fintype I] (c : I → Chains V) (v : V) :
    boundary (meanChain c) v = (Fintype.card I : ℝ)⁻¹ * ∑ i, boundary (c i) v := by
  unfold boundary meanChain
  simp only [← mul_sub, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

theorem mass_edge_difference_le {G : SimpleGraph V} (p : V → Chains V)
    (u v : V) (R : ℝ) (hr : dualNorm (triangleChain (G := G)) (orientedEdge u v + p u - p v) ≤ R) :
    mass (p v - p u) ≤ 1 + 3 * R := by
  have h := mass_sub_le (orientedEdge u v) (orientedEdge u v + p u - p v)
  rw [show orientedEdge u v - (orientedEdge u v + p u - p v) = p v - p u by abel] at h
  linarith [mass_orientedEdge_le u v, mass_le_dualNorm (triangleChain_mass (G := G)) (orientedEdge u v + p u - p v)]

theorem mass_walk_difference_le {G : SimpleGraph V} (p : V → Chains V) (D : ℝ)
    (h : ∀ u v, G.Adj u v → mass (p v - p u) ≤ D)
    {u v : V} (P : G.Walk u v) : mass (p v - p u) ≤ (P.length : ℝ) * D := by
  induction P with
  | nil => simp [mass]
  | @cons u x v hux P ih =>
    have hs := mass_add (p v - p x) (p x - p u)
    rw [show p v - p x + (p x - p u) = p v - p u by abel] at hs
    exact hs.trans (by push_cast [Walk.length_cons]; linarith [h u x hux])

end Normalization

section LoadsUnderPermutations

variable {V : Type*} [Fintype V]

theorem invariant_load (σ : Equiv.Perm V) (c : Chains V)
    (h : ∀ u v, c (σ u, σ v) = c (u,v)) (v : V) : load c (σ v) = load c v := by
  unfold load
  rw [← Equiv.sum_comp σ (fun u => |c (σ v,u)| + |c (u,σ v)|)]
  simp only [h]

theorem equal_fiber_mass_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Finset V) (f : V → I) (u : V → ℝ) (a : I)
    (h : ∀ b, ∑ v ∈ S with f v = b, u v = ∑ v ∈ S with f v = a, u v) :
    ∑ v ∈ S with f v = a, u v = (Fintype.card I : ℝ)⁻¹ * ∑ v ∈ S, u v := by
  classical
  have hsum : (∑ b : I, ∑ v ∈ S with f v = b, u v) = ∑ v ∈ S, u v := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [show (∑ b : I, ∑ v ∈ S with f v = b, u v) =
    (Fintype.card I : ℝ) * ∑ v ∈ S with f v = a, u v from by simp [h]]
    at hsum
  rw [← hsum, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

end LoadsUnderPermutations

section ChangeOfProjection

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem dualNorm_add_le {T : Type*} (t : T → Chains V) (a b : Chains V) :
    dualNorm t (a + b) ≤ dualNorm t a + dualNorm t b := by
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  rw [pairing_chain_add]
  exact (abs_add_le _ _).trans
    (add_le_add (abs_pairing_le_dualNorm hf a) (abs_pairing_le_dualNorm hf b))

theorem dualNorm_neg_eq {T : Type*} (t : T → Chains V) (a : Chains V) :
    dualNorm t (-a) = dualNorm t a := by
  unfold dualNorm values
  congr 1
  ext r
  simp [pairing, mul_neg, Finset.sum_neg_distrib]

theorem dualNorm_push_change {T : Type*} (t : T → Chains V) (ρ σ : V → V)
    (c : Chains V) (S : Finset V) (h : ∀ u, u ∉ S → ρ u = σ u) :
    dualNorm t (pushChain ρ c - pushChain σ c) ≤ 6 * ∑ u ∈ S, load c u := by
  apply csSup_le (values_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  rw [pairing_chain_sub, pairing_pushChain, pairing_pushChain]
  apply abs_pairing_change_le _ _ _ _ _ (by norm_num)
  · intro e
    apply (abs_sub _ _).trans
    exact (add_le_add (hf.1 _) (hf.1 _)).trans (by norm_num)
  · intro u v hu hv
    simp [pullCochain, h u hu, h v hv]

end ChangeOfProjection

end

end SimpleGraph.ChordalReconstruction
