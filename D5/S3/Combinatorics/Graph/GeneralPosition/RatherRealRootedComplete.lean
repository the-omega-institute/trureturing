/- GID: D5/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/GeneralPosition/RatherRealRootedComplete
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Real-rooted general position polynomials characterize connected complete graphs. -/

/-
proof_shape: result: bind-only (Vieta, frozen Newton, graph metrics and finite counting)
escape_witness: none
admission_basis: open-problem-resolution (#18870; Proved)
Direct frozen dependencies: F1--F3 below, after inlining same-module helpers.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19014
Frozen declaration identities:
F1 = D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.IsGeneralPosition
  @ sha256:0ef36317d75a06b086fd9e6ec9647d7d1f2f1764305f20e5b1e81a609546e2a7
F2 = D5/S3/Combinatorics/Graph/GeneralPosition/CylinderSevenTen.OnGeodesic
  @ sha256:df4af79287634b94d39e0a5f75a43bf8ad5ac32a711c99be991f791714b34ecf
F3 = D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm
  @ sha256:7400c7930c32ea078d27794d6b5042598efcdfa59e1c3509a6ab2f5df4849495
The source expressions for alpha, psi, IsRealRooted and claim are unchanged.
IsGeneralPosition and OnGeodesic are reused from CylinderSevenTen.
Distances are SimpleGraph.dist; the classification is restricted to connected graphs.
The public surface consists of four definitions and the settling result.
Columns: declaration | proof_shape | frozen dependencies | escape_witness | consumers.
The shared admission basis above applies to every row.
alpha | bind-only | F1 | none | psi,alpha_of_small,alpha_top,alpha_full
psi | bind-only | F1 | none | IsRealRooted,coeff_psi,degree_psi,psi_top,full_of_real_rooted
IsRealRooted | bind-only | F1 | none | claim,full_of_real_rooted,top_real_rooted
claim | bind-only | F1 | none | result
gp_small | bind-only | F1,F2 | none | alpha_of_small,full_of_real_rooted
gp_top | bind-only | F1,F2 | none | alpha_top
complete_of_gp_univ | bind-only | F1,F2 | none | result
alpha_of_small | bind-only | F1,F2 | none | full_of_real_rooted
alpha_top | bind-only | F1,F2 | none | psi_top
coeff_psi | bind-only | F1 | none | degree_psi,psi_top,full_of_real_rooted
degree_psi | bind-only | F1 | none | full_of_real_rooted
psi_top | bind-only | F1,F2 | none | top_real_rooted
alpha_full | bind-only | F1 | none | full_of_real_rooted
reflected_splits | bind-only | none | none | full_of_real_rooted
monic_coeff_zero_ne | bind-only | F3 | none | full_of_real_rooted
full_of_real_rooted | bind-only | F1,F2,F3 | none | result
top_real_rooted | bind-only | F1,F2 | none | result
result | bind-only | F1,F2,F3 | none | none
-/

import D5.S3.Analytic.RealRootedCoefficientNewton
import Mathlib.Analysis.Complex.Polynomial.Basic
import D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted

open Polynomial SimpleGraph
open D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen (IsGeneralPosition)

variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- "For each k ≥ 0, let α_k(G) denote the number of general position sets of size k"
(B. A. Rather, arXiv:2603.06930, Section 2). -/
noncomputable def alpha (G : SimpleGraph V) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter fun S => S.card = k ∧ IsGeneralPosition G S).card

/-- "The general position polynomial of G is ψ(G) = ∑_{k≥0} α_k(G)x^k" (ibid.); α_k(G) = 0 for
k > |V(G)|. -/
noncomputable def psi (G : SimpleGraph V) : ℤ[X] :=
  ∑ k ∈ Finset.range (Fintype.card V + 1), C (alpha G k : ℤ) * X ^ k

/-- ψ(G) has only real zeros. -/
def IsRealRooted (G : SimpleGraph V) : Prop :=
  ∀ z : ℂ, aeval z (psi G) = 0 → z.im = 0

/-- B. A. Rather, arXiv:2603.06930v3, Section 8, item 1: "For no nontrivial family is it currently
known whether ψ(G) is always real-rooted." Answer for connected graphs: ψ(G) is real-rooted if and
only if G is complete. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), Nonempty V → G.Connected →
    (IsRealRooted G ↔ G = ⊤)

end D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted

namespace D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted
variable {V : Type} [Fintype V]
open D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen (OnGeodesic IsGeneralPosition)
open Polynomial SimpleGraph

omit [Fintype V] in
private theorem gp_small (G : SimpleGraph V) (S : Finset V) (hS : S.card ≤ 2) :
    IsGeneralPosition G S := by
  classical
  intro u hu v hv w hw huv hvw huw
  have hsub : {u,v,w} ⊆ S := by simp_all [Finset.insert_subset_iff]
  have hc : ({u,v,w} : Finset V).card = 3 := Finset.card_triple_eq_three_iff.mpr ⟨huv, huw, hvw⟩
  have := Finset.card_le_card hsub
  omega

omit [Fintype V] in
private theorem gp_top (S : Finset V) : IsGeneralPosition (⊤ : SimpleGraph V) S := by
  intro u hu v hv w hw huv hvw huw
  simp [OnGeodesic, SimpleGraph.dist_top_of_ne, huv, hvw, huw]

private theorem complete_of_gp_univ (G : SimpleGraph V) (hconn : G.Connected)
    (hgp : IsGeneralPosition G Finset.univ) : G = ⊤ := by
  classical
  apply top_unique
  intro u v huv
  by_contra hnot
  have hne : u ≠ v := huv
  obtain ⟨p,hp⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨a,b,c,hab,hbc,hac,hneac⟩ := p.exists_adj_adj_not_adj_ne hp (hconn.one_lt_dist_of_ne_of_not_adj hne hnot)
  have hd : G.dist a c = 2 := by
    have he := (SimpleGraph.edist_eq_two_iff).mpr ⟨hneac,hac,b,hab,hbc.symm⟩
    have hr := hab.reachable.trans hbc.reachable
    have he' := hr.coe_dist_eq_edist
    rw [he] at he'
    exact_mod_cast he'
  apply hgp a (Finset.mem_univ _) b (Finset.mem_univ _) c (Finset.mem_univ _)
    hab.ne hbc.ne hneac
  unfold OnGeodesic
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hab,SimpleGraph.dist_eq_one_iff_adj.mpr hbc,hd]

end D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted

namespace D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted
open Polynomial SimpleGraph
open D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen (IsGeneralPosition)
variable {V : Type} [Fintype V]

private theorem alpha_of_small (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 2) :
    alpha G k = (Fintype.card V).choose k := by
  classical
  have he : (Finset.univ.filter (fun S : Finset V => S.card = k ∧ IsGeneralPosition G S)) =
      (Finset.univ : Finset V).powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard, Finset.subset_univ]
    exact ⟨fun h => h.1,fun h => ⟨h,gp_small G S (by omega)⟩⟩
  simp [alpha,he]

private theorem alpha_top (k : ℕ) : alpha (⊤ : SimpleGraph V) k = (Fintype.card V).choose k := by
  classical
  have he : (Finset.univ.filter (fun S : Finset V => S.card = k ∧ IsGeneralPosition (⊤ : SimpleGraph V) S)) =
      (Finset.univ : Finset V).powersetCard k := by
    ext S
    simp [gp_top, Finset.mem_powersetCard]
  simp [alpha,he]

private theorem coeff_psi (G : SimpleGraph V) (k : ℕ) :
    (psi G).coeff k = if k ≤ Fintype.card V then (alpha G k : ℤ) else 0 := by
  classical
  simp [psi,finsetSum_coeff]

private theorem degree_psi (G : SimpleGraph V) : (psi G).natDegree ≤ Fintype.card V := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [coeff_psi,not_le.mpr hk]

private theorem psi_top : psi (⊤ : SimpleGraph V) = (1 + X) ^ Fintype.card V := by
  ext k
  rw [coeff_psi,coeff_one_add_X_pow,alpha_top]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl

private theorem alpha_full (G : SimpleGraph V) (h : alpha G (Fintype.card V) ≠ 0) :
    IsGeneralPosition G Finset.univ := by
  classical
  obtain ⟨S,hS⟩ := Finset.card_ne_zero.mp h
  have hs := (Finset.mem_filter.mp hS).2
  have he : S = Finset.univ := Finset.eq_univ_of_card S hs.1
  simpa [he] using hs.2

end D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted


namespace D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted
open Polynomial

private theorem reflected_splits (p : ℝ[X]) (n : ℕ) (hn : p.natDegree ≤ n)
    (hr : ∀ z : ℂ, eval₂ (algebraMap ℝ ℂ) z p = 0 → z.im = 0) :
    (p.reflect n).Splits := by
  let q := p.reflect n
  apply (IsAlgClosed.splits (q.map (algebraMap ℝ ℂ))).of_splits_map_of_injective
    (algebraMap ℝ ℂ).injective
  intro z hz
  have he : eval₂ (algebraMap ℝ ℂ) z q = 0 := by
    rw [← eval_map]
    exact (mem_roots'.mp hz).2
  have hi : z.im = 0 := by
    by_cases h0 : z = 0
    · simp [h0]
    · let _ := invertibleOfNonzero (inv_ne_zero h0)
      have hh := eval₂_reflect_eq_zero_iff (algebraMap ℝ ℂ) z⁻¹ n p hn
      have hz' : eval₂ (algebraMap ℝ ℂ) z⁻¹ p = 0 := by
        apply hh.mp
        simpa [q] using he
      have hi' := hr _ hz'
      have hreal : z⁻¹ = (z⁻¹).re := by
        apply Complex.ext <;> simp [hi']
      have hhreal := congrArg (fun x : ℂ => x⁻¹) hreal
      rw [inv_inv,← Complex.ofReal_inv] at hhreal
      rw [hhreal]
      simp
  refine ⟨z.re, ?_⟩
  apply Complex.ext <;> simp [hi]

private theorem monic_coeff_zero_ne (q : ℝ[X]) (n : ℕ) (hn : 2 ≤ n)
    (hm : q.Monic) (hd : q.natDegree = n) (hs : q.Splits)
    (h1 : q.coeff (n-1) = n) (h2 : q.coeff (n-2) = (n.choose 2 : ℝ)) :
    q.coeff 0 ≠ 0 := by
  have hc : q.roots.card = n := by rw [hs.natDegree_eq_card_roots.symm,hd]
  have hv1 := coeff_eq_esymm_roots_of_splits hs (k := n-1) (by omega)
  have hv2 := coeff_eq_esymm_roots_of_splits hs (k := n-2) (by omega)
  rw [hm.leadingCoeff,hd,Nat.sub_sub_self (by omega : 1 ≤ n)] at hv1
  rw [hm.leadingCoeff,hd,Nat.sub_sub_self hn] at hv2
  have hs1 : q.roots.esymm 1 = -(n : ℝ) := by rw [h1] at hv1; norm_num at hv1; linarith
  have hs2 : 2 * q.roots.esymm 2 = (n : ℝ) * (n-1 : ℝ) := by
    rw [h2,Nat.cast_choose_two] at hv2
    norm_num at hv2
    linarith
  intro hz
  have hzmem : (0 : ℝ) ∈ q.roots := (Polynomial.mem_roots hm.ne_zero).mpr
    (by simpa only [Polynomial.IsRoot,Polynomial.coeff_zero_eq_eval_zero] using hz)
  let s := q.roots.erase 0
  have he : (0 : ℝ) ::ₘ s = q.roots := Multiset.cons_erase hzmem
  have hsc : s.card = n-1 := by
    dsimp [s]
    rw [Multiset.card_erase_of_mem hzmem,hc,Nat.pred_eq_sub_one]
  have hzero_esymm (k : ℕ) : ((0 : ℝ) ::ₘ s).esymm (k+1) = s.esymm (k+1) := by
    simp [Multiset.esymm]
  have he1 : s.esymm 1 = -(n : ℝ) := by
    rw [← hzero_esymm 0,he]
    exact hs1
  have he2 : 2 * s.esymm 2 = (n : ℝ) * (n-1 : ℝ) := by
    rw [← hzero_esymm 1,he]
    exact hs2
  have hnew := D5.S3.Analytic.RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm s 0
  have hscr : (s.card : ℝ) = (n : ℝ)-1 := by
    rw [hsc,Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  simp only [Nat.cast_zero,zero_add,sub_zero,Multiset.esymm_zero,one_mul] at hnew
  rw [hscr,he1] at hnew
  nlinarith [show (0 : ℝ) < n from Nat.cast_pos.mpr (by omega)]

end D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted

namespace D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted
open Polynomial SimpleGraph
open D5.S3.Combinatorics.Graph.GeneralPosition.CylinderSevenTen (IsGeneralPosition)
variable {V : Type} [Fintype V]

private theorem full_of_real_rooted (G : SimpleGraph V) (hr : IsRealRooted G) :
    IsGeneralPosition G Finset.univ := by
  classical
  by_cases hsmall : Fintype.card V ≤ 2
  · exact gp_small G Finset.univ (by simpa)
  have hn : 2 ≤ Fintype.card V := Nat.le_of_not_ge hsmall
  let n := Fintype.card V
  let p : ℝ[X] := (psi G).map (Int.castRingHom ℝ)
  have hpn : p.natDegree ≤ n := (natDegree_map_le).trans (degree_psi G)
  let q := p.reflect n
  have hcoeff (k : ℕ) (hk : k ≤ n) : q.coeff (n-k) = (alpha G k : ℝ) := by
    simp only [q, coeff_reflect, revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk]
    simp [p,coeff_psi,show k ≤ Fintype.card V from hk]
  have hqn : q.coeff n = 1 := by
    simpa [alpha_of_small G 0 (by omega)] using hcoeff 0 (by omega)
  have hd : q.natDegree = n := by
    apply le_antisymm
    · exact (natDegree_reflect_le).trans (max_le (le_refl n) hpn)
    · exact le_natDegree_of_ne_zero (by rw [hqn]; norm_num)
  have hm : q.Monic := by
    show q.leadingCoeff = 1
    rw [leadingCoeff,hd,hqn]
  have hs : q.Splits := by
    apply reflected_splits p n hpn
    intro z hz
    apply hr z
    have heq : (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = algebraMap ℤ ℂ := Subsingleton.elim _ _
    simpa only [p,Polynomial.eval₂_map,Polynomial.aeval_def,heq] using hz
  have hq1 : q.coeff (n-1) = (n : ℝ) := by
    rw [hcoeff 1 (by omega),alpha_of_small G 1 (by omega)]
    simp [n]
  have hq2 : q.coeff (n-2) = (n.choose 2 : ℝ) := by
    rw [hcoeff 2 hn,alpha_of_small G 2 (by omega)]
  have hq0 := monic_coeff_zero_ne q n hn hm hd hs hq1 hq2
  apply alpha_full G
  intro hz
  apply hq0
  have hh := hcoeff n (le_refl n)
  simpa only [Nat.sub_self,show alpha G n = 0 from hz,Nat.cast_zero] using hh

private theorem top_real_rooted : IsRealRooted (⊤ : SimpleGraph V) := by
  intro z hz
  rw [psi_top] at hz
  simp only [map_pow,map_add,map_one,aeval_X] at hz
  have hh : 1 + z = 0 := (eq_zero_of_pow_eq_zero hz)
  have he : z = -1 := eq_neg_of_add_eq_zero_right hh
  simp [he]

theorem result : D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted.claim := by
  intro V _ _ G hnonempty hconn
  constructor
  · intro hr
    exact complete_of_gp_univ G hconn (full_of_real_rooted G hr)
  · intro he
    subst G
    exact top_real_rooted

end D5.S3.Combinatorics.Graph.GeneralPosition.RatherRealRootedComplete.RatherGPRealRooted
