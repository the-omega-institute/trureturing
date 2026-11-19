/- GID: D5/S1/Words/ReturnWords/ShortReturnWidthTransport
   generality: G
   mirror-B: D5/B/S1/Words/ReturnWords/ShortReturnWidthTransport
   mirror-E: none(waiver:abstract-return-width-estimate)
   anchors: []
   utility: none
   digest: Finite interval chains supply packing bounds for short-return width transport. -/

import D5.S1.Words.ReturnWords.CoherentReturnPathTemplates
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

/-! Finite start-chain packing and phase-bounded conditional width transport. -/

namespace D5.S1.Words.ReturnWords.ShortReturnWidthTransport

/-- Adjacent separation accumulates along a finite chain of interval starts.
The final interval has length `ℓ`; only the first and last endpoints are constrained
by the parent. The conclusion is derived from local inequalities by induction. -/
theorem finite_interval_chain_packing {k : ℕ} (x : ℕ → ℝ) {δ ℓ u w : ℝ}
    (hleft : u ≤ x 0)
    (hstep : ∀ i < k, x i + δ ≤ x (i + 1))
    (hright : x k + ℓ ≤ u + w) :
    (k : ℝ) * δ + ℓ ≤ w := by
  have accumulated : ∀ m ≤ k, x 0 + (m : ℝ) * δ ≤ x m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hm
        have hprev := ih (Nat.le_trans (Nat.le_succ m) hm)
        have hnext := hstep m (Nat.lt_of_succ_le hm)
        rw [Nat.cast_succ]
        linarith
  have htotal := accumulated k le_rfl
  linarith

/-- Affine images of a finite separated interval chain lie inside a parent interval.
The inclusion concerns the width-`w` images. The separate length-`d` intervals
`[x i, x i + d]` are ordered with disjoint interiors, allowing touching endpoints.
No claim identifies these abstract intervals with legal graph cylinders. -/
theorem affine_cylinder_chain_packing {k L : ℕ} {g d w u : ℝ} (x : ℕ → ℝ)
    (hg : 0 < g) (hw : 0 ≤ w)
    (hinside : ∀ i ≤ k,
      Set.Icc (u + g ^ L * x i) (u + g ^ L * (x i + w)) ⊆ Set.Icc u (u + w))
    (hseparated : ∀ i < k, x i + d ≤ x (i + 1)) :
    (k : ℝ) * (g ^ L * d) ≤ (1 - g ^ L) * w := by
  have hq : 0 ≤ g ^ L := (pow_pos hg L).le
  have hlen : 0 ≤ g ^ L * w := mul_nonneg hq hw
  have hend (i : ℕ) : u + g ^ L * x i ≤ u + g ^ L * (x i + w) := by
    nlinarith
  have hleft := (hinside 0 (Nat.zero_le k) ⟨le_rfl, hend 0⟩).1
  have hright := (hinside k le_rfl ⟨hend k, le_rfl⟩).2
  have hstep : ∀ i < k,
      (u + g ^ L * x i) + g ^ L * d ≤ u + g ^ L * x (i + 1) := by
    intro i hi
    have hscaled := mul_le_mul_of_nonneg_left (hseparated i hi) hq
    nlinarith
  have htotal := finite_interval_chain_packing
    (fun i => u + g ^ L * x i) (δ := g ^ L * d) (ℓ := g ^ L * w)
    (u := u) (w := w) hleft hstep (by nlinarith [hright])
  nlinarith

/-- Arithmetic synchronization bound for two lengths divisible by a common phase period.
No existence of graph returns is asserted. Natural division is floor division. -/
theorem synchronized_length_le_phase_bound {a b n p : ℕ} (hp : 0 < p)
    (hpa : p ∣ a) (hpb : p ∣ b) (ha : a ≤ n) (hb : b ≤ 2 * n - 1) :
    Nat.lcm a b ≤ p * (n / p) * ((2 * n - 1) / p) := by
  obtain ⟨α, rfl⟩ := hpa
  obtain ⟨γ, rfl⟩ := hpb
  have hα : α ≤ n / p := (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using ha)
  have hγ : γ ≤ (2 * n - 1) / p :=
    (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hb)
  have hlcm : Nat.lcm α γ ≤ α * γ := by
    by_cases hαzero : α = 0
    · simp [hαzero]
    by_cases hγzero : γ = 0
    · simp [hγzero]
    exact Nat.lcm_le_mul (Nat.pos_of_ne_zero hαzero) (Nat.pos_of_ne_zero hγzero)
  rw [Nat.lcm_mul_left]
  calc
    p * Nat.lcm α γ ≤ p * (α * γ) := Nat.mul_le_mul_left p hlcm
    _ ≤ p * ((n / p) * ((2 * n - 1) / p)) :=
      Nat.mul_le_mul_left p (Nat.mul_le_mul hα hγ)
    _ = p * (n / p) * ((2 * n - 1) / p) := (Nat.mul_assoc _ _ _).symm

/-- A longer positive synchronization scale gives a smaller contraction lower bound.
Both denominators are positive, including when the two scales are equal. -/
theorem contraction_ratio_antitone {g : ℝ} (hg : 0 < g) (hgone : g < 1)
    {L M : ℕ} (hL : 0 < L) (hLM : L ≤ M) :
    g ^ M / (1 - g ^ M) ≤ g ^ L / (1 - g ^ L) := by
  have hpow : g ^ M ≤ g ^ L := pow_le_pow_of_le_one hg.le hgone.le hLM
  have hden : 0 < 1 - g ^ L := sub_pos.mpr (pow_lt_one₀ hg.le hgone (Nat.ne_of_gt hL))
  exact div_le_div₀ (pow_nonneg hg.le L) hpow hden (sub_le_sub_left hpow 1)

/-- Conditional width bridge for short returns. The graph/source argument must supply
positive lengths, phase divisibility, the short-return bounds and the packing estimate
at their actual least common multiple. This theorem supplies none of those premises. -/
theorem short_return_width_lower_bound {a b n p : ℕ} {g d w : ℝ}
    (hg : 0 < g) (hgone : g < 1) (hd : 0 ≤ d) (hp : 0 < p)
    (ha0 : 0 < a) (hb0 : 0 < b) (hpa : p ∣ a) (hpb : p ∣ b)
    (ha : a ≤ n) (hb : b ≤ 2 * n - 1)
    (hpacking : g ^ Nat.lcm a b * d ≤ (1 - g ^ Nat.lcm a b) * w) :
    g ^ (p * (n / p) * ((2 * n - 1) / p)) /
      (1 - g ^ (p * (n / p) * ((2 * n - 1) / p))) * d ≤ w := by
  have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
  have hLM := synchronized_length_le_phase_bound hp hpa hpb ha hb
  have hratio := contraction_ratio_antitone hg hgone hL hLM
  have hden : 0 < 1 - g ^ Nat.lcm a b :=
    sub_pos.mpr (pow_lt_one₀ hg.le hgone (Nat.ne_of_gt hL))
  calc
    _ ≤ (g ^ Nat.lcm a b / (1 - g ^ Nat.lcm a b)) * d :=
      mul_le_mul_of_nonneg_right hratio hd
    _ = (g ^ Nat.lcm a b * d) / (1 - g ^ Nat.lcm a b) := by ring
    _ ≤ w := (div_le_iff₀ hden).2 (by simpa [mul_comm] using hpacking)


/-- Derive the packing premise of `short_return_width_lower_bound` from a finite
chain of affine interval images. There are `k+1` starts and `k` gaps; `k=1`
recovers the two-cylinder bound. No actual graph return or legal cylinder is constructed. -/
theorem short_return_width_lower_bound_of_chain {a b n p k : ℕ} {g d w u : ℝ}
    (x : ℕ → ℝ) (hg : 0 < g) (hgone : g < 1) (hd : 0 ≤ d) (hw : 0 ≤ w) (hp : 0 < p)
    (ha0 : 0 < a) (hb0 : 0 < b) (hpa : p ∣ a) (hpb : p ∣ b)
    (ha : a ≤ n) (hb : b ≤ 2 * n - 1)
    (hinside : ∀ i ≤ k,
      Set.Icc (u + g ^ Nat.lcm a b * x i) (u + g ^ Nat.lcm a b * (x i + w)) ⊆
        Set.Icc u (u + w))
    (hseparated : ∀ i < k, x i + d ≤ x (i + 1)) :
    g ^ (p * (n / p) * ((2 * n - 1) / p)) /
      (1 - g ^ (p * (n / p) * ((2 * n - 1) / p))) * ((k : ℝ) * d) ≤ w := by
  have hpacking := affine_cylinder_chain_packing x hg hw hinside hseparated
  apply short_return_width_lower_bound hg hgone (mul_nonneg (Nat.cast_nonneg k) hd)
    hp ha0 hb0 hpa hpb ha hb
  nlinarith [hpacking]

open Quiver Quiver.Path Set D5.S1.Words.Powers
open D5.S1.Words.ReturnWords.CoherentReturnPathTemplates

universe u v w

private theorem exists_nodup_path {V : Type u} [Quiver.{v} V] {a b : V}
    (p : Path a b) : ∃ q : Path a b, q.vertices.Nodup := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons b c p e ih =>
      obtain ⟨q, hq⟩ := ih
      by_cases hc : c ∈ q.vertices
      · obtain ⟨r, s, hr⟩ := q.exists_eq_comp_of_mem_vertices hc
        refine ⟨r, ?_⟩
        rw [hr, Path.vertices_comp] at hq
        have hs : s.vertices = c :: s.vertices.tail := by
          have he := List.cons_head_tail s.vertices_ne_nil
          rw [s.vertices_head_eq] at he
          exact he.symm
        rw [hs] at hq
        change (r.vertices.dropLast ++ ([c] ++ s.vertices.tail)).Nodup at hq
        rw [← List.append_assoc, r.dropLast_append_end_eq] at hq
        exact (List.nodup_append'.mp hq).1
      · refine ⟨q.cons e, ?_⟩
        rw [Path.vertices_cons, List.concat_eq_append, List.nodup_append']
        exact ⟨hq, by simp, by simpa [List.disjoint_left] using hc⟩

private theorem exists_short_path {V : Type u} [Quiver.{v} V] [Finite V] {a b : V}
    (p : Path a b) : ∃ q : Path a b, q.length < Nat.card V := by
  let _ := Fintype.ofFinite V
  obtain ⟨q, hq⟩ := exists_nodup_path p
  refine ⟨q, ?_⟩
  have h := Fintype.card_le_of_injective q.vertices.get hq.injective_get
  rw [Fintype.card_fin, Path.vertices_length] at h
  simpa [Nat.card_eq_fintype_card] using (Nat.lt_of_succ_le h)

private theorem exists_short_positive_return {V : Type u} [Quiver.{v} V] [Finite V] {a : V}
    (p : Path a a) (hp : 0 < p.length) :
    ∃ q : Path a a, 0 < q.length ∧ q.length ≤ Nat.card V := by
  obtain ⟨b, e, r, _, _⟩ := p.length_ne_zero_iff_eq_comp.mp (Nat.ne_of_gt hp)
  obtain ⟨s, hs⟩ := exists_short_path r
  refine ⟨e.toPath.comp s, ?_, ?_⟩ <;> simp only [Path.length_comp, Path.length_toPath] <;> omega

private theorem exists_bounded_detecting_returns
    {V : Type u} [Quiver.{v} V] [Finite V]
    {α : Type w} (label : EdgeLabel V α) (S : StronglyConnectedComponent V)
    (hcyclic : Cyclic S) (hbad : ¬ Coherent label S) (q : Component S) :
    ∃ C D : Path q q,
      0 < C.length ∧ C.length ≤ Nat.card (Component S) ∧
      0 < D.length ∧ D.length ≤ 2 * Nat.card (Component S) - 1 ∧
      wordPower (Nat.lcm C.length D.length / C.length) (output (componentLabel label S) C) ≠
      wordPower (Nat.lcm C.length D.length / D.length) (output (componentLabel label S) D) := by
  classical
  let W := Component S
  let ℓ : EdgeLabel W α := componentLabel label S
  have connected : IsStronglyConnected W := by
    intro a b
    obtain ⟨H⟩ := (StronglyConnectedComponent.mk_eq_mk.mp
      (a.property.trans b.property.symm)).1
    exact ⟨(liftComponentPath S H a.property b.property).val⟩
  have positive : ∃ C : Path q q, 0 < C.length := by
    obtain ⟨r, C, hC⟩ := hcyclic
    obtain ⟨A⟩ := connected q r
    obtain ⟨B⟩ := connected r q
    refine ⟨A.comp (C.comp B), ?_⟩
    simp only [Path.length_comp]
    omega
  obtain ⟨P, hP⟩ := positive
  obtain ⟨C, hCpos, hCbound⟩ := exists_short_positive_return P hP
  let n := Nat.card W
  let bound := 2 * n - 1
  have hconn (a b : W) : ∃ A : Path a b, A.length < n := by
    obtain ⟨A⟩ := connected a b
    exact exists_short_path A
  choose A hA using hconn q
  choose B hB using fun a => hconn a q
  let comparison (D : Path q q) : Prop :=
    wordPower (Nat.lcm C.length D.length / C.length) (output ℓ C) =
    wordPower (Nat.lcm C.length D.length / D.length) (output ℓ D)
  by_cases h : ∃ D : Path q q, 0 < D.length ∧ D.length ≤ bound ∧ ¬ comparison D
  · obtain ⟨D, hDpos, hDbound, hD⟩ := h
    exact ⟨C, D, hCpos, hCbound, hDpos, hDbound, hD⟩
  have hsync (D : Path q q) (hDpos : 0 < D.length) (hDbound : D.length ≤ bound) :
      comparison D := by
    by_contra he
    exact h ⟨D, hDpos, hDbound, he⟩
  exfalso
  apply hbad
  apply (coherent_component_phases label S hcyclic).1.mpr
  have outcons {a b c : W} (H : Path a b) (e : b ⟶ c) :
      output ℓ (H.cons e) = output ℓ H ++ [ℓ e] := by
    simp only [output, Path.weight_cons, FreeMonoid.toList_mul,
      FreeMonoid.of, FreeMonoid.toList_ofList]
  have outcomp {a b c : W} (H : Path a b) (J : Path b c) :
      output ℓ (H.comp J) = output ℓ H ++ output ℓ J :=
    congrArg FreeMonoid.toList (Path.weight_comp _ H J)
  have outlen {a b : W} (H : Path a b) : (output ℓ H).length = H.length := by
    induction H with
    | nil => simp [output]
    | cons H e ih => simp only [outcons, List.length_append, List.length_singleton,
        Path.length_cons, ih]
  let X : Stream' (Option α) := fun i => (output ℓ C)[i % C.length]?
  let shift : Stream' (Option α) → Stream' (Option α) := fun Y i => Y (i + 1)
  have shift_iter (Y : Stream' (Option α)) (k i : Nat) :
      (shift^[k] Y) i = Y (i + k) := by
    induction k generalizing i with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (shift^[k] Y) (i + 1) = _
      rw [ih]; congr 1; omega
  have common (D : Path q q) (hDpos : 0 < D.length) (hDbound : D.length ≤ bound) (i : Nat) :
      X i = (output ℓ D)[i % D.length]? := by
    let L := Nat.lcm C.length D.length
    have ht : i % L < L := Nat.mod_lt _ (Nat.lcm_pos hCpos hDpos)
    have hc : L / C.length * (output ℓ C).length = L := by
      rw [outlen]; exact Nat.div_mul_cancel (Nat.dvd_lcm_left _ _)
    have hd : L / D.length * (output ℓ D).length = L := by
      rw [outlen]; exact Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
    have heq := congrArg (fun U : List α => U[i % L]?) (hsync D hDpos hDbound)
    rw [wordPower_getElem? _ _ _ (by rw [hc]; exact ht),
      wordPower_getElem? _ _ _ (by rw [hd]; exact ht), outlen, outlen,
      Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_left _ _),
      Nat.mod_mod_of_dvd _ (Nat.dvd_lcm_right _ _)] at heq
    exact heq
  have periodC : Function.IsPeriodicPt shift C.length X := by
    funext i
    rw [shift_iter]
    simp only [X, Nat.add_mod_right]
  let p := Function.minimalPeriod shift X
  have hp := periodC.minimalPeriod_pos hCpos
  have hple := periodC.minimalPeriod_le hCpos
  let _ : NeZero p := ⟨hp.ne'⟩
  have retdiv (D : Path q q) (hDbound : D.length ≤ bound) : p ∣ D.length := by
    by_cases hD : 0 < D.length
    · have hperiod : Function.IsPeriodicPt shift D.length X := by
        funext i
        rw [shift_iter, common D hD hDbound, common D hD hDbound, Nat.add_mod_right]
      exact hperiod.minimalPeriod_dvd
    · have hz : D.length = 0 := by omega
      rw [hz]; exact dvd_zero p
  have modX (i : Nat) : X (i % p) = X i := by
    have heq := congrFun (Function.iterate_mod_minimalPeriod_eq (f := shift) (x := X)
      (n := i)) 0
    simpa only [shift_iter, Nat.zero_add] using heq
  have letters (z : ZMod p) : ∃ a : α, X z.val = some a := by
    have hz : z.val < C.length := (ZMod.val_lt z).trans_le hple
    dsimp only [X]
    rw [Nat.mod_eq_of_lt hz]
    exact ⟨(output ℓ C)[z.val]'(by rw [outlen]; exact hz),
      List.getElem?_eq_getElem (by rw [outlen]; exact hz)⟩
  let F : ZMod p → α := fun z => (letters z).choose
  have F_eq (i : Nat) : some (F (i : ZMod p)) = X i := by
    rw [← modX i]
    exact (letters (i : ZMod p)).choose_spec.symm.trans
      (congrArg X (ZMod.val_natCast p i))
  let θ : W → ZMod p := fun a => (A a).length
  refine ⟨p, hp, hple.trans hCbound, F, θ, ?_⟩
  intro a b e
  let T := ((A a).cons e).comp (B b)
  have htlen : T.length = (A a).length + 1 + (B b).length := by
    simp only [T, Path.length_comp, Path.length_cons]
  have hTpos : 0 < T.length := by omega
  have hTbound : T.length ≤ bound := by
    have := hA a
    have := hB b
    dsimp only [bound]
    omega
  have hvertex : ((A b).comp (B b)).length ≤ bound := by
    have := hA b
    have := hB b
    simp only [Path.length_comp, bound]
    omega
  have hzEdge := (ZMod.natCast_eq_zero_iff _ _).mpr (retdiv T hTbound)
  have hzVertex := (ZMod.natCast_eq_zero_iff _ _).mpr (retdiv _ hvertex)
  rw [htlen, Nat.cast_add, Nat.cast_add, Nat.cast_one] at hzEdge
  simp only [Path.length_comp, Nat.cast_add] at hzVertex
  refine ⟨?_, add_right_cancel (hzVertex.trans hzEdge.symm)⟩
  have hi : (A a).length < T.length := by omega
  have hchar := (common T hTpos hTbound (A a).length).symm
  rw [Nat.mod_eq_of_lt hi] at hchar
  change (output ℓ (((A a).cons e).comp (B b)))[(A a).length]? = _ at hchar
  rw [outcomp, List.getElem?_append_left (by rw [outlen, Path.length_cons]; omega),
    outcons, List.getElem?_append_right (by rw [outlen]), outlen, Nat.sub_self] at hchar
  simp only [List.getElem?_cons_zero] at hchar
  exact Option.some.inj (hchar.trans (F_eq (A a).length).symm)

private theorem mem_affine_image_Ioo {m c a b y : ℝ} (hm : m ≠ 0)
    (hy : y ∈ Ioo (c + m * (if 0 < m then a else b))
      (c + m * (if 0 < m then b else a))) :
    y ∈ (fun x : ℝ => c + m * x) '' Ioo a b := by
  refine ⟨(y - c) / m, ?_, ?_⟩
  · by_cases hp : 0 < m
    · simp only [hp, ite_true, mem_Ioo] at hy
      exact ⟨(lt_div_iff₀ hp).2 (by linarith [hy.1]),
        (div_lt_iff₀ hp).2 (by linarith [hy.2])⟩
    · have hn : m < 0 := lt_of_le_of_ne (le_of_not_gt hp) hm
      simp only [hp, ite_false, mem_Ioo] at hy
      exact ⟨(lt_div_iff_of_neg hn).2 (by linarith [hy.2]),
        (div_lt_iff_of_neg hn).2 (by linarith [hy.1])⟩
  · field_simp
    ring

private theorem signed_two_cylinder_packing {k a b u v c₁ c₂ : ℝ}
    (hk : k ≠ 0) (hab : a < b) (huv : u ≤ v)
    (h₁ : MapsTo (fun x : ℝ => c₁ + k * x) (Icc u v) (Icc u v))
    (h₂ : MapsTo (fun x : ℝ => c₂ + k * x) (Icc u v) (Icc u v))
    (hdis : Disjoint ((fun x : ℝ => c₁ + k * x) '' Ioo a b)
      ((fun x : ℝ => c₂ + k * x) '' Ioo a b)) :
    |k| * (b - a) ≤ (1 - |k|) * (v - u) := by
  let ga := if 0 < k then a else b
  let gb := if 0 < k then b else a
  have guardWidth : k * gb - k * ga = |k| * (b - a) := by
    by_cases hn : 0 < k
    · simp only [ga, gb, hn, ite_true, abs_of_pos hn]
      ring
    · have hneg : k < 0 := lt_of_le_of_ne (le_of_not_gt hn) hk
      simp only [ga, gb, hn, ite_false, abs_of_neg hneg]
      ring
  have hg : k * ga < k * gb := by
    have hq : 0 < |k| * (b - a) := mul_pos (abs_pos.mpr hk) (sub_pos.mpr hab)
    linarith
  have ordered (c d : ℝ) (hcd : c ≤ d)
      (hc : MapsTo (fun x : ℝ => c + k * x) (Icc u v) (Icc u v))
      (hd : MapsTo (fun x : ℝ => d + k * x) (Icc u v) (Icc u v))
      (hCD : Disjoint ((fun x : ℝ => c + k * x) '' Ioo a b)
        ((fun x : ℝ => d + k * x) '' Ioo a b)) :
      |k| * (b - a) ≤ (1 - |k|) * (v - u) := by
    have gap : c + k * gb ≤ d + k * ga := by
      by_contra! hoverlap
      let mid := (d + k * ga + (c + k * gb)) / 2
      have hcmid : mid ∈ Ioo (c + k * ga) (c + k * gb) :=
        ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩
      have hdmid : mid ∈ Ioo (d + k * ga) (d + k * gb) :=
        ⟨by dsimp [mid]; linarith, by dsimp [mid]; linarith⟩
      exact Set.disjoint_left.mp hCD (mem_affine_image_Ioo hk hcmid)
        (mem_affine_image_Ioo hk hdmid)
    by_cases hp : 0 < k
    · have hlo := (hc ⟨le_rfl, huv⟩).1
      have hhi := (hd ⟨huv, le_rfl⟩).2
      change u ≤ c + k * u at hlo
      change d + k * v ≤ v at hhi
      rw [abs_of_pos hp] at *
      linarith only [hlo, hhi, gap, guardWidth]
    · have hn : k < 0 := lt_of_le_of_ne (le_of_not_gt hp) hk
      have hlo := (hc ⟨huv, le_rfl⟩).1
      have hhi := (hd ⟨le_rfl, huv⟩).2
      change u ≤ c + k * v at hlo
      change d + k * u ≤ v at hhi
      rw [abs_of_neg hn] at *
      linarith only [hlo, hhi, gap, guardWidth]
  rcases le_total c₁ c₂ with h | h
  · exact ordered c₁ c₂ h h₁ h₂ hdis
  · exact ordered c₂ c₁ h h₂ h₁ hdis.symm

private theorem length_returnPower {W : Type u} [Quiver.{v} W] {q : W}
    (C : Path q q) (i : Nat) : (returnPower C i).length = i * C.length := by
  induction i with
  | zero => simp [returnPower]
  | succ i hi => simp only [returnPower, Path.length_comp, hi, Nat.succ_mul]; omega

private theorem output_returnPower {W : Type u} [Quiver.{v} W] {α : Type w}
    (label : EdgeLabel W α) {q : W} (C : Path q q) (i : Nat) :
    output label (returnPower C i) = wordPower i (output label C) := by
  induction i with
  | zero => simp [returnPower, output]
  | succ i hi =>
      have hcomp : output label (C.comp (returnPower C i)) =
          output label C ++ output label (returnPower C i) :=
        congrArg FreeMonoid.toList (Path.weight_comp _ C _)
      rw [returnPower, hcomp, hi, wordPower_succ]

private theorem phase_dvd_return {W : Type u} [Quiver.{v} W] {p : Nat}
    (phase : W → ZMod p)
    (hphase : ∀ {x y : W}, (x ⟶ y) → phase y = phase x + 1)
    {q : W} (C : Path q q) : p ∣ C.length := by
  have phase_path {x y : W} (A : Path x y) : phase y = phase x + (A.length : ZMod p) := by
    induction A with
    | nil => simp
    | cons A e hi => rw [hphase e, hi, Path.length_cons, Nat.cast_succ, add_assoc]
  have hz : (C.length : ZMod p) = 0 := by
    have heq : phase q + (C.length : ZMod p) = phase q + 0 := by
      simpa only [add_zero] using (phase_path C).symm
    exact add_left_cancel heq
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

/-- A separate edge phase and the guard/piece image laws give a width bound
at every basepoint of an incoherent cyclic component. -/
theorem width_at_incoherent_basepoint
    {V : Type u} [Quiver.{v} V] [Finite V] {α : Type w}
    (label : EdgeLabel V α) (S : StronglyConnectedComponent V)
    (hcyclic : Cyclic S) (hbad : ¬ Coherent label S) (q : Component S)
    {g ga gb l r : ℝ} (hg : 0 < g) (hg1 : g < 1) (hguard : ga < gb) (hpiece : l ≤ r)
    {p : Nat} (hp : 0 < p) (phase : Component S → ZMod p)
    (hphase : ∀ {x y : Component S}, (x ⟶ y) → phase y = phase x + 1)
    (offset : Path q q → ℝ)
    (hmap : ∀ C : Path q q,
      MapsTo (fun x : ℝ => offset C + (-g) ^ C.length * x) (Icc l r) (Icc l r))
    (hseparate : ∀ C D : Path q q, C.length = D.length →
      output (componentLabel label S) C ≠ output (componentLabel label S) D →
      Disjoint
        ((fun x : ℝ => offset C + (-g) ^ C.length * x) '' Ioo ga gb)
        ((fun x : ℝ => offset D + (-g) ^ D.length * x) '' Ioo ga gb)) :
    g ^ (p * (Nat.card (Component S) / p) * ((2 * Nat.card (Component S) - 1) / p)) /
      (1 - g ^ (p * (Nat.card (Component S) / p) * ((2 * Nat.card (Component S) - 1) / p))) *
      (gb - ga) ≤ r - l := by
  obtain ⟨C, D, hCpos, hCb, hDpos, hDb, hword⟩ :=
    exists_bounded_detecting_returns label S hcyclic hbad q
  let L := Nat.lcm C.length D.length
  let C' := returnPower C (L / C.length)
  let D' := returnPower D (L / D.length)
  have hC'L : C'.length = L := by
    rw [length_returnPower]; exact Nat.div_mul_cancel (Nat.dvd_lcm_left _ _)
  have hD'L : D'.length = L := by
    rw [length_returnPower]; exact Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
  have hwords : output (componentLabel label S) C' ≠ output (componentLabel label S) D' := by
    rw [output_returnPower, output_returnPower]
    exact hword
  have hcmap := hmap C'
  have hdmap := hmap D'
  have hdis := hseparate C' D' (hC'L.trans hD'L.symm) hwords
  rw [hC'L] at hcmap hdis
  rw [hD'L] at hdmap hdis
  have hpack := signed_two_cylinder_packing (pow_ne_zero _ (neg_ne_zero.mpr hg.ne'))
    hguard hpiece hcmap hdmap hdis
  rw [abs_pow, abs_neg, abs_of_pos hg] at hpack
  exact short_return_width_lower_bound hg hg1 (sub_nonneg.mpr hguard.le) hp
    hCpos hDpos (phase_dvd_return phase hphase C) (phase_dvd_return phase hphase D)
    hCb hDb hpack

end D5.S1.Words.ReturnWords.ShortReturnWidthTransport
