/- GID: D5/S3/Topology/GraphChainAveraging
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-sharp-four-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Projection, normalization, and symmetrization of finite real graph chains. -/

import OmegaBuild.Commands
import D5.S3.Topology.FiniteGraphChainNorm

compile_only_with_mathlib

/-! Omega original.

Projection, normalization, and symmetrization of finite real graph chains. -/

namespace Omega.GraphChains

open scoped BigOperators

noncomputable section

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
    (fixed : ∀ x y, x ∉ S → y ∉ S → c (x,y) ≠ 0 → a (x,y) = b (x,y)) :
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
    · by_cases he : c e = 0
      · simp [he, hx, hy]
      · rw [show a e = b e from fixed e.1 e.2 hx hy he]
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
    exact hs.trans (by push_cast [SimpleGraph.Walk.length_cons]; linarith [h u x hux])

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
  · intro u v hu hv _
    simp [pullCochain, h u hu, h v hv]

end ChangeOfProjection

end

end Omega.GraphChains
