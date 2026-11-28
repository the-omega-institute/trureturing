/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalGroupCoefficient
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrality of the universal group gain reconstruction coefficient. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.Chordal.UniformGainPotential
import D5.S3.Combinatorics.Graph.Chordal.ChordalWalkHolonomy
import Mathlib.Algebra.Order.Floor.Ring
import D5.S3.Combinatorics.Graph.GroupWordMetric
import Mathlib.GroupTheory.FreeGroup.Basic

compile_only_with_mathlib

/-!
Omega original.

The integral universal coefficient from a canonical free-group cochain.
-/

namespace SimpleGraph.GroupCoefficient

open GroupWordMetric

universe u
variable {V : Type u} {G T : SimpleGraph V}

/-- Admissible universal error bounds at triangle defect one. -/
def Admissible (G : SimpleGraph V) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (H : Type u) [Group H] [PseudoMetricSpace H] [IsIsometricSMul H H]
    [IsIsometricSMul Hᵐᵒᵖ H] (g : V → V → H),
    (∀ a b, G.Adj a b → g b a = (g a b)⁻¹) →
    (∀ a b c, G.Adj a b → G.Adj b c → G.Adj a c →
      Dist.dist (g a b * g b c) (g a c) ≤ 1) →
    ∃ p : V → H, ∀ a b, G.Adj a b → Dist.dist (g a b) ((p a)⁻¹ * p b) ≤ C

private abbrev Generator (G T : SimpleGraph V) [LT V] :=
  {e : V × V // e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ ¬ T.Adj e.1 e.2}

private noncomputable def freeGain [LinearOrder V] (G T : SimpleGraph V) (a b : V) :
    FreeGroup (Generator G T) := by
  classical
  exact if h : a < b ∧ G.Adj a b ∧ ¬ T.Adj a b then FreeGroup.of ⟨(a,b),h⟩
    else if h : b < a ∧ G.Adj b a ∧ ¬ T.Adj b a then (FreeGroup.of ⟨(b,a),h⟩)⁻¹
    else 1

private theorem freeGain_rev [LinearOrder V] (a b : V) :
    freeGain G T b a = (freeGain G T a b)⁻¹ := by
  classical
  by_cases hab : a < b ∧ G.Adj a b ∧ ¬ T.Adj a b
  · have hba : ¬ (b < a ∧ G.Adj b a ∧ ¬ T.Adj b a) := fun h => hab.1.not_gt h.1
    simp [freeGain, hab, hba]
  · by_cases hba : b < a ∧ G.Adj b a ∧ ¬ T.Adj b a <;> simp [freeGain, hab, hba]

private theorem freeGain_tree [LinearOrder V] (a b : V) (h : T.Adj a b) :
    freeGain G T a b = 1 := by
  classical
  simp [freeGain, h, h.symm]

private def normalTriangles {H : Type*} [Group H] (G : SimpleGraph V) (g : V → V → H) :
    Set H := {x | ∃ a b c q, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
      x = q * (g a b * g b c * g c a) * q⁻¹}

private theorem normalTriangles_inv {H : Type*} [Group H] {g : V → V → H}
    (hr : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹) :
    ∀ x ∈ normalTriangles G g, x⁻¹ ∈ normalTriangles G g := by
  rintro _ ⟨a,b,c,q,hab,hbc,hca,rfl⟩
  refine ⟨a,c,b,q,hca.symm,hbc.symm,hab.symm,?_⟩
  rw [hr a b hab, hr b c hbc, hr c a hca]
  group

private theorem normalTriangles_conj {H : Type*} [Group H] {g : V → V → H} (p : H) :
    ∀ x ∈ normalTriangles G g, p * x * p⁻¹ ∈ normalTriangles G g := by
  rintro _ ⟨a,b,c,q,hab,hbc,hca,rfl⟩
  exact ⟨a,b,c,p*q,hab,hbc,hca,by group⟩

private theorem canonical_generates [Finite V] [LinearOrder V] (hG : G.IsChordal)
    (hTG : T ≤ G) (hT : T.IsTree) : Generates (normalTriangles G (freeGain G T)) := by
  classical
  intro x
  induction x using FreeGroup.induction_on with
  | one => exact ⟨0, Fits.one⟩
  | of e =>
    obtain ⟨⟨a,b⟩,hab,hg,ht⟩ := e
    let p : T.Walk b a := (hT.connected b a).some
    let q := p.map (show T →g G from ⟨id, fun h => hTG h⟩)
    have hp : p.gain (freeGain G T) = 1 := by
      have he := p.gain_of_potential (freeGain G T) (fun _ => 1) (fun a b hab => by
        simp [freeGain_tree a b hab])
      simpa using he
    have hq : q.gain (freeGain G T) = 1 := (Walk.gain_map_id hTG (freeGain G T) p).trans hp
    obtain ⟨n, _, hcert⟩ := hG.closed_walk_triangle_product (freeGain G T)
      (fun a b _ => freeGain_rev a b) (q.cons hg)
    obtain ⟨l, _, he, hmem⟩ := hcert.exists_factors
    simp only [Walk.gain_cons, hq, mul_one] at he
    have hval : freeGain G T a b = FreeGroup.of ⟨(a,b),hab,hg,ht⟩ := by
      rw [freeGain, dite_eq_left ⟨hab,hg,ht⟩]
    exact ⟨l.length, l, hmem, le_rfl, he.trans hval⟩
  | inv_of e ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, hn.inv (normalTriangles_inv (fun a b _ => freeGain_rev a b))⟩
  | mul x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    exact ⟨m+n, hm.mul hn⟩

private theorem eval_freeGain [LinearOrder V] {H : Type*} [Group H]
    (g : V → V → H) (hrev : ∀ a b, G.Adj a b → g b a = (g a b)⁻¹)
    (hzero : ∀ a b, T.Adj a b → g a b = 1) (a b : V) (h : G.Adj a b) :
    FreeGroup.lift (fun e : Generator G T => g e.val.1 e.val.2) (freeGain G T a b) = g a b := by
  classical
  by_cases ht : T.Adj a b
  · rw [freeGain_tree a b ht, hzero a b ht, map_one]
  · rcases lt_or_gt_of_ne h.ne with hab | hba
    · simp [freeGain, hab, h, ht, FreeGroup.lift_apply_of]
    · have ht' : ¬ T.Adj b a := fun ht' => ht ht'.symm
      simp [freeGain, hba, hba.not_gt, h.symm, ht', hrev a b h]

private theorem map_word_bound {H A : Type*} [Group H] [Group A]
    [PseudoMetricSpace A] [IsIsometricSMul A A] {S : Set H} (F : H →* A)
    (hF : ∀ x ∈ S, Dist.dist (F x) 1 ≤ 1)
    {n : ℕ} {x : H} (hx : Fits S n x) : Dist.dist (F x) 1 ≤ (n : ℝ) := by
  obtain ⟨l, hl, hn, rfl⟩ := hx
  have hlen (l : List H) (hh : ∀ x ∈ l, x ∈ S) : Dist.dist (F l.prod) 1 ≤ (l.length : ℝ) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have h₁ := hF a (hh a List.mem_cons_self)
      have h₂ := ih (fun x hx => hh x (List.mem_cons_of_mem a hx))
      have h₃ := _root_.dist_triangle (F a * F l.prod) (F a) 1
      rw [show Dist.dist (F a * F l.prod) (F a) = Dist.dist (F l.prod) 1 by simpa only [mul_one] using dist_mul_left (F a) (F l.prod) 1] at h₃
      simp only [List.prod_cons, map_mul, List.length_cons, Nat.cast_succ]
      linarith
  exact (hlen l hl).trans (by exact_mod_cast hn)


/-- The least real bound for a finite connected chordal graph is a nonnegative integer.
The universal group may be taken to be the free group on the oriented cotree edges,
with length measured in conjugates of canonical triangle holonomies. -/
theorem integral [Finite V] [LinearOrder V] (hG : G.IsChordal) (hconn : G.Connected) :
    ∃ k : ℕ, k ≤ 4 ∧ ∀ C : ℝ, Admissible G C ↔ (k : ℝ) ≤ C := by
  classical
  obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
  let g₀ := freeGain G T
  let U := normalTriangles G g₀
  have hrev₀ (a b : V) (_ : G.Adj a b) : g₀ b a = (g₀ a b)⁻¹ := freeGain_rev a b
  have hInv := normalTriangles_inv hrev₀
  have hConj := normalTriangles_conj (G := G) (g := g₀)
  have hGen : Generates U := canonical_generates hG hTG hT
  let := metric hGen hInv
  let := left_isometric hGen hInv
  let := right_isometric hGen hInv hConj
  let Pass (n : ℕ) := ∃ p : V → FreeGroup (Generator G T),
    ∀ a b, G.Adj a b → Fits U n (p a * g₀ a b * (p b)⁻¹)
  have hd (x y : FreeGroup (Generator G T)) :
      Dist.dist x y = (length hGen (x * y⁻¹) : ℝ) := by
    change (length hGen (x⁻¹ * y) : ℝ) = _
    rw [← length_inv hGen hInv (x⁻¹ * y), mul_inv_rev, inv_inv]
    rw [← length_conj hGen hConj x (y⁻¹ * x)]
    congr 1
    group
  have he (p : V → FreeGroup (Generator G T)) (a b : V) :
      Dist.dist (g₀ a b) ((p a)⁻¹ * p b) = (length hGen (p a * g₀ a b * (p b)⁻¹) : ℝ) := by
    rw [gain_error_eq_fit, hd]
  have htri₀ (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
      Dist.dist (g₀ a b * g₀ b c) (g₀ a c) ≤ 1 := by
    rw [hd, ← hrev₀ a c hac]
    have hm : g₀ a b * g₀ b c * g₀ c a ∈ U :=
      ⟨a,b,c,1,hab,hbc,hac.symm,by simp⟩
    have hf := (length_le_iff hGen 1 _).2 (Fits.of_mem hm)
    exact_mod_cast hf
  have h4 : Pass 4 := by
    obtain ⟨p,hp⟩ := hG.exists_uniform_approximate_gain_potential g₀ 1 (by norm_num) hrev₀ htri₀
    refine ⟨p, fun a b hab => (length_le_iff hGen 4 _).1 ?_⟩
    have hh := hp a b hab
    rw [he] at hh
    norm_num at hh
    exact_mod_cast hh
  let k := Nat.find (show ∃ n, Pass n from ⟨4,h4⟩)
  have hk : Pass k := Nat.find_spec (show ∃ n, Pass n from ⟨4,h4⟩)
  refine ⟨k, Nat.find_min' (show ∃ n, Pass n from ⟨4,h4⟩) h4, fun C => ?_⟩
  constructor
  · intro hC
    obtain ⟨p,hp⟩ := hC.2 _ g₀ hrev₀ htri₀
    have hpass : Pass ⌊C⌋₊ := by
      refine ⟨p, fun a b hab => (length_le_iff hGen _ _).1 ?_⟩
      have hh := hp a b hab
      rw [he] at hh
      exact (Nat.le_floor_iff hC.1).2 hh
    have hmin : k ≤ ⌊C⌋₊ := Nat.find_min' (show ∃ n, Pass n from ⟨4,h4⟩) hpass
    exact (Nat.cast_le.mpr hmin).trans (Nat.floor_le hC.1)
  · intro hC
    refine ⟨(Nat.cast_nonneg k).trans hC, fun H _ _ _ _ g hrev htri => ?_⟩
    obtain ⟨a,ha⟩ := hT.isAcyclic.exists_gain_potential g (fun a b h => hrev a b (hTG h))
    let f (u v : V) := a u * g u v * (a v)⁻¹
    have hfrev (u v : V) (h : G.Adj u v) : f v u = (f u v)⁻¹ := by
      dsimp [f]
      rw [hrev u v h]
      group
    let F := FreeGroup.lift (fun e : Generator G T => f e.val.1 e.val.2)
    have hF (u v : V) (h : G.Adj u v) : F (g₀ u v) = f u v :=
      eval_freeGain f hfrev (fun u v h => by dsimp [f]; rw [ha u v h]; group) u v h
    have hFU : ∀ x ∈ U, Dist.dist (F x) 1 ≤ 1 := by
      rintro _ ⟨u,v,w,q,huv,hvw,hwu,rfl⟩
      simp only [map_mul, map_inv, hF u v huv, hF v w hvw, hF w u hwu]
      dsimp [f]
      have he' :
          F q * (a u * g u v * (a v)⁻¹ * (a v * g v w * (a w)⁻¹) *
            (a w * g w u * (a u)⁻¹)) * (F q)⁻¹ =
          (F q * a u) * (g u v * g v w * g w u) * (F q * a u)⁻¹ := by group
      rw [he']
      rw [show (1 : H) = (F q * a u) * 1 * (F q * a u)⁻¹ by group,
        dist_mul_right, dist_mul_left, hrev u w hwu.symm]
      rw [show (1 : H) = g u w * (g u w)⁻¹ by simp, dist_mul_right]
      exact htri u v w huv hvw hwu.symm
    obtain ⟨p,hp⟩ := hk
    let φ (v : V) := F (p v) * a v
    refine ⟨φ, fun u v huv => ?_⟩
    have hh := map_word_bound F hFU (hp u v huv)
    rw [map_mul, map_mul, map_inv, hF u v huv] at hh
    have he' :
        F (p u) * f u v * (F (p v))⁻¹ = φ u * g u v * (φ v)⁻¹ := by dsimp [f,φ]; group
    rw [he'] at hh
    rw [gain_error_eq_fit, ← dist_mul_right _ _ (φ v)⁻¹, mul_inv_cancel]
    exact hh.trans hC

end SimpleGraph.GroupCoefficient
