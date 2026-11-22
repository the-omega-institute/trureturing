/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedRankTwoParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedRankTwoParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dual.Lemmas, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Bipartite]
   utility: none
   digest: One binary linear parity equation selects the target switching class among exact factors at residual rank two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination

/-! A linear parity test for the rank-two switching quotient on fixed-degree factors. -/

set_option autoImplicit false

open scoped BigOperators Matrix
open LinearMap
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity

private abbrev Bit := ZMod 2

private def weight {E : Type*} [Fintype E] (x : E → Bit) : ℤ :=
  ∑ e, ((x e).val : ℤ)

private theorem val_add (x y : Bit) :
    ((x + y).val : ℤ) = x.val + y.val - 2 * (x.val * y.val : ℤ) := by
  fin_cases x <;> fin_cases y <;> decide

private theorem weight_add {E : Type*} [Fintype E] (x y : E → Bit) :
    weight (x + y) = weight x + weight y - 2 * (∑ e, (x e).val * (y e).val : ℤ) := by
  simp only [weight, Pi.add_apply, val_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]

private theorem dot_self {E : Type*} [Fintype E] (x : E → Bit) :
    x ⬝ᵥ x = ∑ e, x e := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro e _
  exact (show ∀ a : Bit, a * a = a by decide) (x e)

private theorem cast_weight {E : Type*} [Fintype E] (x : E → Bit) :
    (weight x : Bit) = ∑ e, x e := by
  simp [weight, Int.cast_sum]

private theorem cast_overlap {E : Type*} [Fintype E] (x y : E → Bit) :
    ((∑ e, (x e).val * (y e).val : ℤ) : Bit) = x ⬝ᵥ y := by
  simp [dotProduct, Int.cast_sum, Int.cast_mul]

private def exchangeQuadratic {E : Type*} [Fintype E] (F c : E → Bit) : Bit :=
  ((weight c / 2 : ℤ) : Bit) + F ⬝ᵥ c

private theorem exchange_vanishes {E : Type*} [Fintype E] (F F' : E → Bit)
    (hweight : weight F' = weight F) :
    exchangeQuadratic F (F + F') = 0 := by
  have hhalf : weight (F + F') / 2 =
      weight F - (∑ e, (F e).val * (F' e).val : ℤ) := by
    rw [weight_add, hweight]
    omega
  have hs : F ⬝ᵥ F = (weight F : Bit) := by rw [dot_self, cast_weight]
  rw [exchangeQuadratic, hhalf, Int.cast_sub, cast_overlap, dotProduct_add, hs]
  have h := ZModModule.add_self (weight F : Bit)
  linear_combination h

private theorem exchange_polar {E : Type*} [Fintype E] (F c d : E → Bit)
    (hc : ∑ e, c e = 0) (hd : ∑ e, d e = 0) :
    exchangeQuadratic F (c + d) =
      exchangeQuadratic F c + exchangeQuadratic F d + c ⬝ᵥ d := by
  have evenWeight (x : E → Bit) (hx : ∑ e, x e = 0) : weight x % 2 = 0 := by
    rw [← cast_weight] at hx
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (weight x) 2).mp hx
    omega
  have hce := evenWeight c hc
  have hde := evenWeight d hd
  have hhalf : weight (c + d) / 2 =
      weight c / 2 + weight d / 2 - (∑ e, (c e).val * (d e).val : ℤ) := by
    rw [weight_add]
    omega
  simp only [exchangeQuadratic, hhalf, Int.cast_sub, Int.cast_add, cast_overlap, dotProduct_add,
    ZModModule.sub_eq_add]
  abel

private theorem bipartite_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {L R : Set V} [DecidablePred (· ∈ L)] (hpart : G.IsBipartiteWith L R)
    {K : Type*} [Semiring K] (x : G.edgeSet → K) :
    ∑ v ∈ Finset.univ.filter (· ∈ L), (∑ e : G.edgeSet, G.incMatrix K v e.val * x e) =
      ∑ e, x e := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨e, he⟩ := e
  revert he
  refine Sym2.ind (fun a b he _ => ?_) e
  have edges := G.mem_edgeSet.mp he
  have unique (a b : V) (ha : a ∈ L) (hb : b ∈ R) (hab : G.Adj a b) :
      ∑ v ∈ Finset.univ.filter (· ∈ L), G.incMatrix K v s(a, b) *
        x ⟨s(a, b), G.mem_edgeSet.mpr hab⟩ = x ⟨s(a, b), G.mem_edgeSet.mpr hab⟩ := by
    have hb' : b ∉ L := fun h => Set.disjoint_left.mp hpart.disjoint h hb
    rw [Finset.sum_eq_single a]
    · simp [SimpleGraph.incMatrix_apply', hab]
    · intro v hv hva
      have hvb : v ≠ b := fun eq => hb' (eq ▸ (Finset.mem_filter.mp hv).2)
      simp [SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff, hva, hvb]
    · simp [ha]
  rcases hpart.mem_of_adj edges with h | h
  · exact unique a b h.1 h.2 edges
  · simpa only [Sym2.eq_swap] using unique b a h.2 h.1 edges.symm

private theorem dot_represented {E : Type*} [Fintype E] (f : (E → Bit) →ₗ[Bit] Bit) :
    ∃ u : E → Bit, dotProductBilin Bit Bit u = f := by
  classical
  refine ⟨fun e => f (Pi.single e 1), ?_⟩
  apply LinearMap.ext
  intro x
  change (∑ e, f (Pi.single e 1) * x e) = f x
  have hx : (∑ e, x e • Pi.single e (1 : Bit)) = x := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc
    _ = f (∑ e, x e • Pi.single e (1 : Bit)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [map_smul, smul_eq_mul, mul_comm]
    _ = f x := congrArg f hx

private theorem cut_iff_orthogonal {V E : Type*} [Fintype V] [Fintype E]
    (B : Matrix V E Bit) (x : E → Bit) :
    x ∈ range Bᵀ.mulVecLin ↔ ∀ c : Cycles B, x ⬝ᵥ c.val = 0 := by
  constructor
  · rintro ⟨y, rfl⟩ c
    rw [dotProduct_comm, Matrix.mulVecLin_apply, Matrix.dotProduct_transpose_mulVec]
    rw [← Matrix.mulVecLin_apply, mem_ker.mp c.property, dotProduct_zero]
  · intro orthogonal
    have h : dotProductBilin Bit Bit x ∈ (Cycles B).dualAnnihilator :=
      (Submodule.mem_dualAnnihilator _).mpr (fun c hc => orthogonal ⟨c, hc⟩)
    rw [← B.mulVecLin.range_dualMap_eq_dualAnnihilator_ker] at h
    obtain ⟨f, hf⟩ := h
    obtain ⟨y, rfl⟩ := dot_represented f
    refine ⟨y, sub_eq_zero.mp (dotProduct_eq_zero_iff.mp ?_)⟩
    intro c
    have he := DFunLike.congr_fun hf c
    change y ⬝ᵥ (B *ᵥ c) = x ⬝ᵥ c at he
    rw [sub_dotProduct, Matrix.mulVecLin_apply, dotProduct_comm (Bᵀ *ᵥ y),
      Matrix.dotProduct_transpose_mulVec, he, sub_self]

private theorem rank_two_coordinates {V E : Type*} [Fintype V] [Fintype E]
    (B : Matrix V E Bit) (hRank : residualRank B = 2)
    (hEven : ∀ c : Cycles B, ∑ e, c.val e = 0)
    (t : Cycles B) (ht : t.val ∉ range Bᵀ.mulVecLin) :
    ∃ p : Cycles B →ₗ[Bit] Bit × Bit,
      p t = (1, 0) ∧ ker p = bicycles B ∧
        ∀ c d : Cycles B, c.val ⬝ᵥ d.val = (p c).1 * (p d).2 + (p c).2 * (p d).1 := by
  classical
  obtain ⟨u, hu⟩ := not_forall.mp (fun h => ht ((cut_iff_orthogonal B t.val).mpr h))
  have htu : t.val ⬝ᵥ u.val = 1 :=
    (show ∀ a : Bit, a ≠ 0 → a = 1 by decide) _ hu
  let p := ((dotProductBilin Bit Bit u.val).comp (Cycles B).subtype).prod
    ((dotProductBilin Bit Bit t.val).comp (Cycles B).subtype)
  have pt : p t = (1, 0) := by
    change (u.val ⬝ᵥ t.val, t.val ⬝ᵥ t.val) = _
    rw [dotProduct_comm u.val, htu, dot_self, hEven]
  have pu : p u = (0, 1) := by
    change (u.val ⬝ᵥ u.val, t.val ⬝ᵥ u.val) = _
    rw [dot_self, hEven, htu]
  have hp (a b : Bit) : p (a • t + b • u) = (a, b) := by
    simp [map_add, map_smul, pt, pu]
  have hle : bicycles B ≤ ker p := by
    intro c hc
    have hcut : c.val ∈ range Bᵀ.mulVecLin := hc.2
    have hz := (cut_iff_orthogonal B c.val).mp hcut
    exact mem_ker.mpr (Prod.ext (by simpa [p, dotProduct_comm] using hz u)
      (by simpa [p, dotProduct_comm] using hz t))
  let pQ := (bicycles B).liftQ p hle
  have hinj : Function.Injective pQ := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    · rintro ⟨a, b⟩
      exact ⟨(bicycles B).mkQ (a • t + b • u), hp a b⟩
    · change residualRank B = Module.finrank Bit (Bit × Bit)
      rw [hRank, Module.finrank_prod, Module.finrank_self]
  have hker : ker p = bicycles B := by
    apply le_antisymm _ hle
    intro c hc
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hinj
    simpa [pQ] using mem_ker.mp hc
  refine ⟨p, pt, hker, fun c d => ?_⟩
  let c' := (p c).1 • t + (p c).2 • u
  have hdiff : c - c' ∈ bicycles B := by
    rw [← hker, mem_ker, map_sub, show p c' = p c from hp _ _, sub_self]
  have horth := (cut_iff_orthogonal B (c - c').val).mp hdiff.2 d
  change (c.val - c'.val) ⬝ᵥ d.val = 0 at horth
  rw [sub_dotProduct, sub_eq_zero] at horth
  rw [horth]
  change ((p c).1 • t.val + (p c).2 • u.val) ⬝ᵥ d.val = _
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
  rfl

/-- For a fixed exact factor and a parity-compatible reference in a different switching class,
one edge functional detects precisely the exact factors in the reference class. -/
theorem exact_factor_switching_iff_parity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hpart : G.IsBipartite)
    (hRank : residualRank (incidence G) = 2)
    (q : V → ℤ) (F w₀ : G.edgeSet → ZMod 2) (hF : negativeDegree G F = q)
    (hParity : (incidence G).mulVecLin w₀ = fun v => (q v : ZMod 2))
    (hDifferent : F + w₀ ∉ range (incidence G)ᵀ.mulVecLin) :
    ∃ ell : (G.edgeSet → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      ∀ F', negativeDegree G F' = q →
        (F' + w₀ ∈ range (incidence G)ᵀ.mulVecLin ↔ ell (F + F') = 1) := by
  classical
  obtain ⟨L, R, hLR⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hpart
  let B := incidence G
  have even (c : Cycles B) : ∑ e, c.val e = 0 := by
    rw [← bipartite_sum G hLR]
    exact Finset.sum_eq_zero (fun v _ => congrFun (mem_ker.mp c.property) v)
  have parity (w : G.edgeSet → Bit) (hw : negativeDegree G w = q) :
      B.mulVecLin w = B.mulVecLin w₀ := by
    have hReference :
        B.mulVecLin (w₀ + Bᵀ.mulVecLin 0) = fun v => (q v : Bit) := by
      simpa only [map_zero, add_zero] using hParity
    obtain ⟨c, hc⟩ := (exact_signed_rows G w₀ 0 q hReference).1 w hw
    rw [hc, map_zero, add_zero, map_add, mem_ker.mp c.property, add_zero]
  have cycle (w w' : G.edgeSet → Bit) (hw : B.mulVecLin w = B.mulVecLin w') :
      w + w' ∈ Cycles B := by
    rw [mem_ker, map_add, hw]
    exact ZModModule.add_self _
  let t : Cycles B := ⟨F + w₀, cycle F w₀ (parity F hF)⟩
  obtain ⟨p, pt, hker, hdot⟩ := rank_two_coordinates B hRank even t hDifferent
  let indicator (a : Bit × Bit) : Bit := a.1 * (1 + a.2)
  have indicator_iff (a : Bit × Bit) : indicator a = 1 ↔ a = (1, 0) := by
    obtain ⟨a, b⟩ := a
    fin_cases a <;> fin_cases b <;> decide
  let f : Cycles B →ₗ[Bit] Bit :=
    { toFun c := exchangeQuadratic F c.val + indicator (p c)
      map_add' c d := by
        change exchangeQuadratic F (c.val + d.val) + indicator (p (c + d)) = _
        rw [exchange_polar F _ _ (even c) (even d), hdot, map_add]
        simp only [indicator, Prod.fst_add, Prod.snd_add]
        have hcancel : (p c).1 * (p d).2 + (p c).1 * (p d).2 = 0 :=
          ZModModule.add_self _
        have hcancel' : (p c).2 * (p d).1 + (p c).2 * (p d).1 = 0 :=
          ZModModule.add_self _
        linear_combination hcancel + hcancel'
      map_smul' a c := by
        change exchangeQuadratic F (a • c).val + indicator (p (a • c)) =
          a • (exchangeQuadratic F c.val + indicator (p c))
        rcases (show ∀ a : Bit, a = 0 ∨ a = 1 by decide) a with rfl | rfl
        · simp [exchangeQuadratic, weight, indicator]
        · simp }
  obtain ⟨ell, hell⟩ := Subspace.dualRestrict_surjective f
  refine ⟨ell, fun F' hF' => ?_⟩
  let c : Cycles B := ⟨F + F', cycle F F' ((parity F hF).trans (parity F' hF').symm)⟩
  have weight_eq (w : G.edgeSet → Bit) : weight w =
      ∑ v ∈ Finset.univ.filter (· ∈ L), negativeDegree G w v :=
    (bipartite_sum G hLR _).symm
  have hw : weight F' = weight F := by rw [weight_eq F', weight_eq F, hF', hF]
  have he : ell (F + F') = indicator (p c) := by
    have hh := DFunLike.congr_fun hell c
    change ell (F + F') = exchangeQuadratic F (F + F') + indicator (p c) at hh
    simpa only [exchange_vanishes F F' hw, zero_add] using hh
  have hdiff : (c - t).val = F' + w₀ := by
    change F + F' - (F + w₀) = F' + w₀
    rw [ZModModule.sub_eq_add, add_comm F F', ZModModule.add_add_add_cancel]
  rw [he, indicator_iff, ← pt, ← hdiff]
  have hclass : (c - t).val ∈ range Bᵀ.mulVecLin ↔ c - t ∈ bicycles B :=
    ⟨fun h => ⟨(c - t).property, h⟩, fun h => h.2⟩
  rw [hclass, ← hker, mem_ker, map_sub, sub_eq_zero]

#print axioms exact_factor_switching_iff_parity

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedRankTwoParity
