/- GID: D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.claim; result=D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.result; claim=D5/S3/Combinatorics/ReciprocalPairs/GroupGraphReciprocalRefutation.claim
   digest: A sign-coupled union of three edges and two four-cliques refutes Campbell. -/

/-
result
proof_shape: content
escape_witness: none
admission_basis: open-problem-resolution (#16260; Refuted)
Direct frozen dependencies:
  D5/S3/FiniteGroups/NikolovSegal/Equation47TypeIIBounds.actualCycleCount
  sha256:a338d60f4e3e46a495045ebfbc9037ef374866181c5169801ed56591701c05b2
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The cycle polynomial retains the literal SameCycle Fintype.card convention; proofs
use the frozen actualCycleCount through the consumed cycleConvention equality.
Private theorem classifications (all escape witnesses are none):
  parityAct_one: proof_shape: bind-only; consumer: parityHom
  parityAct_mul: proof_shape: bind-only; consumer: parityHom
  isAut_of_block_action: proof_shape: bind-only; consumer: group_aut
  group_aut: proof_shape: bind-only; consumer: result
  no_universal_vertex: proof_shape: bind-only; consumer: not_listed
  not_listed: proof_shape: bind-only; consumer: result
  partition_block_constant: proof_shape: bind-only; consumer: partition_bound
  partition_bound: proof_shape: bind-only; consumer: no_isomorphic_parts
  mate_adj: proof_shape: bind-only; consumer: even_part_card
  mate_sq: proof_shape: bind-only; consumer: even_part_card
  even_part_card: proof_shape: bind-only; consumer: no_isomorphic_parts
  no_isomorphic_parts: proof_shape: bind-only; consumer: irreducible
  rawTop_blocks: proof_shape: bind-only; consumer: rawTop_mem, odd_top_not_even
  rawTop_mem: proof_shape: bind-only; consumer: small_part_eq, large_part_eq, no_product_parts
  swap_fixed: proof_shape: bind-only; consumer: swap_mem, signed_colour_sum
  swap_mem: proof_shape: bind-only; consumer: small_part_eq, large_part_eq, edge_swap_mem
  blocks_witness_unique: proof_shape: bind-only; consumer: odd_top_not_even
  odd_top_not_even: proof_shape: bind-only; consumer: no_product_parts
  fixes_small_even: proof_shape: bind-only; consumer: supported_even
  fixes_large_even: proof_shape: bind-only; consumer: supported_even
  supported_preserves: proof_shape: bind-only; consumer: generated_preserves
  generated_preserves: proof_shape: bind-only; consumer: no_product_parts
  transported_mem: proof_shape: bind-only; consumer: small_part_eq, large_part_eq, no_product_parts, edge_swap_mem
  small_part_eq: proof_shape: bind-only; consumer: layer_labels_distinct, supported_even
  large_part_eq: proof_shape: bind-only; consumer: layer_labels_distinct, supported_even
  layer_labels_distinct: proof_shape: bind-only; consumer: supported_even
  supported_even: proof_shape: bind-only; consumer: no_product_parts
  no_product_parts: proof_shape: content; consumer: irreducible
  irreducible: proof_shape: content; consumer: result
  even_top_cube: proof_shape: bind-only; consumer: proper_fixed_sign
  odd_top_square: proof_shape: bind-only; consumer: proper_fixed_sign
  odd_top_moved: proof_shape: bind-only; consumer: proper_fixed_sign
  block_colouring_injective: proof_shape: bind-only; consumer: proper_fixed_sign
  proper_fixed_sign: proof_shape: content; consumer: reciprocal
  cycleTag_eq_iff: proof_shape: bind-only; consumer: cycleCount_eq
  cycleTag_surjective: proof_shape: bind-only; consumer: cycleCount_eq
  cycleCount_eq: proof_shape: content; consumer: sign_cycleCount
  sign_cycleCount: proof_shape: content; consumer: signed_cycle_total
  fixed_sameCycle: proof_shape: bind-only; consumer: allFixed_card
  allFixed_card: proof_shape: bind-only; consumer: signed_cycle_total
  signed_indicator_cancel: proof_shape: bind-only; consumer: signed_colour_sum
  filter_card_int: proof_shape: bind-only; consumer: reciprocal_of_signed_counting
  signed_colour_sum: proof_shape: bind-only; consumer: reciprocal_of_signed_counting
  cycleConvention: proof_shape: bind-only; consumer: signed_cycle_total
  signed_cycle_total: proof_shape: content; consumer: reciprocal_of_signed_counting
  reciprocal_of_signed_counting: proof_shape: content; consumer: reciprocal
  edge_swap_mem: proof_shape: bind-only; consumer: reciprocal
  reciprocal: proof_shape: content; consumer: result
-/

import D5.S3.FiniteGroups.NikolovSegal.Equation47TypeIIBounds
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open Polynomial
open NikolovSegal.Equation47TypeII (actualCycleCount)
namespace D5.S3.Combinatorics.ReciprocalPairs.GroupGraphReciprocalRefutation
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsAut (Γ : SimpleGraph V) (g : Equiv.Perm V) : Prop :=
  ∀ u v, Γ.Adj (g u) (g v) ↔ Γ.Adj u v

def cyclePoly (G : Subgroup (Equiv.Perm V)) [Fintype G] : Polynomial ℤ := by
  classical
  exact ∑ g : G, X ^ Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (g : Equiv.Perm V)))

def fixedColourings (Γ : SimpleGraph V) (g : Equiv.Perm V) (c : ℕ) :
    Finset (V → Fin c) := by
  classical
  exact Finset.univ.filter fun f =>
    (∀ u v, Γ.Adj u v → f u ≠ f v) ∧ (∀ v, f (g v) = f v)

def IsReciprocal (Γ : SimpleGraph V) (G : Subgroup (Equiv.Perm V))
    [Fintype G] : Prop :=
  ∀ c : ℕ, 0 < c →
    ((∑ g : G, (fixedColourings Γ g c).card : ℕ) : ℤ) =
      (-1) ^ Fintype.card V * (cyclePoly G).eval (-(c : ℤ))

def Reducible (Γ : SimpleGraph V) (G : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ part : V → Fin m,
    Function.Surjective part ∧
    (∀ u v, Γ.Adj u v → part u = part v) ∧
    ((∃ Gi : Fin m → Subgroup (Equiv.Perm V),
      (∀ i, Gi i ≤ G) ∧
      (∀ i g, g ∈ Gi i → ∀ v, part v ≠ i → g v = v) ∧
      Subgroup.closure (⋃ i, (Gi i : Set (Equiv.Perm V))) = G) ∨
    (∀ i j : Fin m,
      Nonempty ((Γ.induce {v | part v = i}) ≃g (Γ.induce {v | part v = j}))))

def IsIrreducible (Γ : SimpleGraph V) (G : Subgroup (Equiv.Perm V)) : Prop :=
  ¬ Reducible Γ G

def Listed (Γ : SimpleGraph V) (_G : Subgroup (Equiv.Perm V)) : Prop :=
  (∀ u v, ¬ Γ.Adj u v) ∨
  (∀ u v, u ≠ v → Γ.Adj u v) ∨
  Nonempty (Γ ≃g SimpleGraph.cycleGraph 4) ∨
  (∃ k : ℕ, 1 ≤ k ∧ k < Fintype.card V ∧ ∃ K : Finset V,
    K.card = k ∧ ∀ u v, Γ.Adj u v ↔ u ≠ v ∧ (u ∈ K ∨ v ∈ K))

def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    (G : Subgroup (Equiv.Perm V)) [Fintype G],
    (∀ g ∈ G, IsAut Γ g) → IsReciprocal Γ G → IsIrreducible Γ G → Listed Γ G


-- The five clique blocks are indexed by (Fin 3 ⊕ Fin 2); their vertices are ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)).
private def blockW : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)) → (Fin 3 ⊕ Fin 2) :=
  Sum.map Prod.fst Prod.fst

private def vertexEquiv : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)) ≃ Fin 14 :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

private def parityAct (h : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 2) :=
  if Equiv.Perm.sign h = 1 then 1 else Equiv.swap 0 1

private theorem parityAct_one : parityAct 1 = 1 := by
  simp [parityAct]

private theorem parityAct_mul (h k : Equiv.Perm (Fin 3)) :
    parityAct (h * k) = parityAct h * parityAct k := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign h) with hh | hh <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign k) with hk | hk <;>
    simp [parityAct, Equiv.Perm.sign_mul, hh, hk]

private def parityHom : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 2) where
  toFun := parityAct
  map_one' := parityAct_one
  map_mul' := parityAct_mul

private def topHom : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3 ⊕ Fin 2) :=
  (Equiv.Perm.sumCongrHom (Fin 3) (Fin 2)).comp
    ((MonoidHom.id _).prod parityHom)

private def H : Subgroup (Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))) where
  carrier := {g | ∃ h : Equiv.Perm (Fin 3),
    ∀ v, blockW (g v) = topHom h (blockW v)}
  one_mem' := by
    refine ⟨1, ?_⟩
    intro v
    simp
  mul_mem' := by
    rintro g k ⟨h, hh⟩ ⟨l, hl⟩
    refine ⟨h * l, ?_⟩
    intro v
    rw [Equiv.Perm.mul_apply, hh, hl, map_mul, Equiv.Perm.mul_apply]
  inv_mem' := by
    rintro g ⟨h, hh⟩
    refine ⟨h⁻¹, ?_⟩
    intro v
    apply (topHom h).injective
    simpa using (hh (g⁻¹ v)).symm

private def G : Subgroup (Equiv.Perm (Fin 14)) :=
  H.map vertexEquiv.permCongrHom.toMonoidHom



private def cliqueGraph {A B : Type*} (b : A → B) : SimpleGraph A :=
  ((⊤ : SimpleGraph B).comap b)ᶜ

private def graph : SimpleGraph (Fin 14) := cliqueGraph (blockW ∘ vertexEquiv.symm)


private theorem isAut_of_block_action {A B : Type*}
    (b : A → B) (g : Equiv.Perm A) (h : Equiv.Perm B)
    (hb : ∀ v, b (g v) = h (b v)) : IsAut (cliqueGraph b) g := by
  intro u v
  simp only [cliqueGraph, SimpleGraph.compl_adj, SimpleGraph.comap_adj,
    SimpleGraph.top_adj, hb, not_ne_iff, ne_eq, g.injective.eq_iff, h.injective.eq_iff]

private theorem group_aut : ∀ g ∈ G, IsAut graph g := by
  intro g hg
  obtain ⟨t, ht, rfl⟩ := hg
  obtain ⟨h, hh⟩ := ht
  apply isAut_of_block_action (blockW ∘ vertexEquiv.symm) _ (topHom h)
  intro v
  simpa [Function.comp_def] using hh (vertexEquiv.symm v)


private theorem no_universal_vertex (u : Fin 14) :
    ∃ v : Fin 14, u ≠ v ∧ ¬ graph.Adj u v := by
  obtain ⟨w, rfl⟩ := vertexEquiv.surjective u
  cases w with
  | inl p =>
    refine ⟨vertexEquiv (.inr (0, 0)), ?_, ?_⟩
    · intro h; have hbad := vertexEquiv.injective h; cases hbad
    · simp [graph, cliqueGraph, Function.comp_def, blockW]
  | inr p =>
    refine ⟨vertexEquiv (.inl (0, 0)), ?_, ?_⟩
    · intro h; have hbad := vertexEquiv.injective h; cases hbad
    · simp [graph, cliqueGraph, Function.comp_def, blockW]

private theorem not_listed : ¬ Listed graph G := by
  rintro (hnull | hcomplete | hcycle | ⟨k, hk, _, K, hK, hAdj⟩)
  · exact hnull 0 1 (by simp only [graph, cliqueGraph, SimpleGraph.compl_adj, SimpleGraph.comap_adj, SimpleGraph.top_adj]; decide)
  · exact (by simp only [graph, cliqueGraph, SimpleGraph.compl_adj, SimpleGraph.comap_adj, SimpleGraph.top_adj]; decide : ¬ graph.Adj 0 2) (hcomplete 0 2 (by decide))
  · obtain ⟨iso⟩ := hcycle
    have hc := Fintype.card_congr iso.toEquiv
    norm_num at hc
  · have hp : 0 < K.card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
    obtain ⟨v, hne, hn⟩ := no_universal_vertex u
    exact hn ((hAdj u v).mpr ⟨hne, Or.inl hu⟩)


private def representative : (Fin 3 ⊕ Fin 2) → Fin 14 :=
  vertexEquiv ∘ Sum.map (fun i => (i, (0 : Fin 2))) (fun i => (i, (0 : Fin 4)))

private theorem partition_block_constant {m : ℕ} (part : Fin 14 → Fin m)
    (he : ∀ u v, graph.Adj u v → part u = part v) (v : Fin 14) :
    part v = part (representative (blockW (vertexEquiv.symm v))) := by
  by_cases hv : v = representative (blockW (vertexEquiv.symm v))
  · exact congrArg part hv
  apply he
  refine ⟨hv, ?_⟩
  apply not_ne_iff.mpr
  cases h : vertexEquiv.symm v with
  | inl p => simp [representative, blockW, h]
  | inr p => simp [representative, blockW, h]

private theorem partition_bound {m : ℕ} (part : Fin 14 → Fin m)
    (hs : Function.Surjective part)
    (he : ∀ u v, graph.Adj u v → part u = part v) : m ≤ 5 := by
  have hr : Function.Surjective (part ∘ representative) := by
    intro i
    obtain ⟨v, rfl⟩ := hs i
    exact ⟨blockW (vertexEquiv.symm v), (partition_block_constant part he v).symm⟩
  simpa using Fintype.card_le_of_surjective (part ∘ representative) hr

private def mate : Equiv.Perm (Fin 14) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 *
    Equiv.swap 6 7 * Equiv.swap 8 9 * Equiv.swap 10 11 * Equiv.swap 12 13

private theorem mate_adj : ∀ v, graph.Adj (mate v) v := by
  simp only [graph, cliqueGraph, SimpleGraph.compl_adj, SimpleGraph.comap_adj,
    SimpleGraph.top_adj]
  decide

private theorem mate_sq : mate ^ 2 = 1 := by decide

private theorem even_part_card {m : ℕ} (part : Fin 14 → Fin m)
    (he : ∀ u v, graph.Adj u v → part u = part v) (i : Fin m) :
    2 ∣ Fintype.card {v // part v = i} := by
  classical
  have hm : ∀ v, part (mate v) = part v := fun v => he _ _ (mate_adj v)
  let r : Equiv.Perm {v // part v = i} :=
    mate.subtypePerm (fun v => by rw [hm v])
  have hr : r ^ 2 = 1 := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    change mate (mate v.val) = v.val
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
      congrArg (fun g : Equiv.Perm (Fin 14) => g v.val) mate_sq
  have hsupport : r.support = Finset.univ := by
    ext v
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro h
    have hv := congrArg Subtype.val h
    exact (mate_adj v.val).1 hv
  simpa [hsupport] using Equiv.Perm.two_dvd_card_support hr

private theorem no_isomorphic_parts {m : ℕ} (hm : 2 ≤ m) (part : Fin 14 → Fin m)
    (hs : Function.Surjective part)
    (he : ∀ u v, graph.Adj u v → part u = part v) :
    ¬ (∀ i j : Fin m,
      Nonempty ((graph.induce {v | part v = i}) ≃g
        (graph.induce {v | part v = j}))) := by
  classical
  intro hi
  let i0 : Fin m := ⟨0, by omega⟩
  let t := Fintype.card {v // part v = i0}
  have hc : ∀ i : Fin m, Fintype.card {v // part v = i} = t := by
    intro i
    obtain ⟨iso⟩ := hi i i0
    exact Fintype.card_congr iso.toEquiv
  have htotal : m * t = 14 := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv part)
    simpa [Fintype.card_sigma, hc] using h
  have heven : 2 ∣ t := even_part_card part he i0
  obtain ⟨r, hr⟩ := heven
  have hb := partition_bound part hs he
  have hm_cases : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hm_cases with h | h | h | h <;> rw [h] at htotal <;> omega


private def rawTop (h : Equiv.Perm (Fin 3)) : Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)) :=
  Equiv.sumCongr (Equiv.prodCongr h (Equiv.refl _))
    (Equiv.prodCongr (parityAct h) (Equiv.refl _))

private theorem rawTop_blocks (h : Equiv.Perm (Fin 3)) (v : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))) :
    blockW (rawTop h v) = topHom h (blockW v) := by
  cases v <;> rfl

private theorem rawTop_mem (h : Equiv.Perm (Fin 3)) : rawTop h ∈ H :=
  ⟨h, rawTop_blocks h⟩

private theorem swap_fixed {A B : Type*} [DecidableEq A] (f : A → B) (u v : A)
    (h : f u = f v) : ∀ w, f (Equiv.swap u v w) = f w := by
  exact Equiv.apply_swap_eq_self h

private theorem swap_mem (u v : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))) (hb : blockW u = blockW v) : Equiv.swap u v ∈ H := by
  refine ⟨1, ?_⟩
  intro w
  simpa using swap_fixed blockW u v hb w

private def evenH : Subgroup (Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))) where
  carrier := {g | ∃ h : Equiv.Perm (Fin 3), Equiv.Perm.sign h = 1 ∧
    ∀ v, blockW (g v) = topHom h (blockW v)}
  one_mem' := by refine ⟨1, by simp, ?_⟩; intro v; simp
  mul_mem' := by
    rintro g k ⟨h, hpos, hh⟩ ⟨l, lpos, hl⟩
    refine ⟨h * l, by simp [hpos, lpos], ?_⟩
    intro v
    rw [Equiv.Perm.mul_apply, hh, hl, map_mul, Equiv.Perm.mul_apply]
  inv_mem' := by
    rintro g ⟨h, hpos, hh⟩
    refine ⟨h⁻¹, by simp [hpos], ?_⟩
    intro v
    apply (topHom h).injective
    simpa using (hh (g⁻¹ v)).symm

private def evenG : Subgroup (Equiv.Perm (Fin 14)) :=
  evenH.map vertexEquiv.permCongrHom.toMonoidHom

private theorem blocks_witness_unique {g : Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))} {h k : Equiv.Perm (Fin 3)}
    (hh : ∀ v, blockW (g v) = topHom h (blockW v))
    (hk : ∀ v, blockW (g v) = topHom k (blockW v)) : h = k := by
  apply Equiv.ext
  intro i
  have e := (hh (.inl (i, 0))).symm.trans (hk (.inl (i, 0)))
  change (Sum.inl (h i) : (Fin 3 ⊕ Fin 2)) = Sum.inl (k i) at e
  exact Sum.inl.inj e

private theorem odd_top_not_even :
    vertexEquiv.permCongrHom (rawTop (Equiv.swap 0 1)) ∉ evenG := by
  rintro ⟨g, ⟨h, hpos, hh⟩, hg⟩
  have heq : g = rawTop (Equiv.swap 0 1) := vertexEquiv.permCongrHom.injective hg
  subst g
  have ht := blocks_witness_unique hh (rawTop_blocks (Equiv.swap 0 1))
  subst h
  simp [Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] at hpos

private theorem fixes_small_even {g : Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))} (hg : g ∈ H)
    (hf : ∀ i j, g (.inl (i, j)) = .inl (i, j)) : g ∈ evenH := by
  obtain ⟨h, hh⟩ := hg
  have hid : h = 1 := by
    apply Equiv.ext
    intro i
    have e := hh (.inl (i, 0))
    rw [hf] at e
    change (Sum.inl i : (Fin 3 ⊕ Fin 2)) = Sum.inl (h i) at e
    exact (Sum.inl.inj e).symm
  exact ⟨h, by simp [hid], hh⟩

private theorem fixes_large_even {g : Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))} (hg : g ∈ H)
    (hf : ∀ i j, g (.inr (i, j)) = .inr (i, j)) : g ∈ evenH := by
  obtain ⟨h, hh⟩ := hg
  have hpos : Equiv.Perm.sign h = 1 := by
    by_contra hn
    have e := hh (.inr (0, 0))
    rw [hf] at e
    have e' : (0 : Fin 2) = parityAct h 0 := Sum.inr.inj e
    simp [parityAct, hn] at e'
  exact ⟨h, hpos, hh⟩


private theorem supported_preserves {A I : Type*} (part : A → I) (i : I)
    (g : Equiv.Perm A) (hf : ∀ v, part v ≠ i → g v = v) :
    ∀ v, part (g v) = part v := by
  intro v
  by_cases hv : part v = i
  · by_cases hgv : part (g v) = i
    · exact hgv.trans hv.symm
    · have heq : g v = v := g.injective (hf (g v) hgv)
      exact False.elim (hgv (by simpa [heq] using hv))
  · rw [hf v hv]

private theorem generated_preserves {m : ℕ} (part : Fin 14 → Fin m)
    (Gi : Fin m → Subgroup (Equiv.Perm (Fin 14)))
    (hf : ∀ i g, g ∈ Gi i → ∀ v, part v ≠ i → g v = v)
    (hgen : Subgroup.closure (⋃ i, (Gi i : Set (Equiv.Perm (Fin 14)))) = G) :
    ∀ g ∈ G, ∀ v, part (g v) = part v := by
  intro g hg
  rw [← hgen] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact supported_preserves part i g (hf i g hi)
  | one => intro v; rfl
  | mul g h _ _ ihg ihh => intro v; exact (ihg (h v)).trans (ihh v)
  | inv g _ ih => intro v; simpa using (ih (g⁻¹ v)).symm


private theorem transported_mem {g : Equiv.Perm ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4))} (hg : g ∈ H) :
    vertexEquiv.permCongrHom g ∈ G := Subgroup.mem_map_of_mem _ hg

private theorem small_part_eq {m : ℕ} (part : Fin 14 → Fin m)
    (hp : ∀ g ∈ G, ∀ v, part (g v) = part v) (i : Fin 3) (j : Fin 2) :
    part ((vertexEquiv (.inl (i, j)))) = part ((vertexEquiv (.inl (0, 0)))) := by
  have hs := hp _ (transported_mem (swap_mem (.inl (i, 0)) (.inl (i, j)) rfl))
    ((vertexEquiv (.inl (i, 0))))
  have hs' : part ((vertexEquiv (.inl (i, j)))) = part ((vertexEquiv (.inl (i, 0)))) := by simpa [] using hs
  have ht := hp _ (transported_mem (rawTop_mem (Equiv.swap 0 i))) ((vertexEquiv (.inl (0, 0))))
  have ht' : part ((vertexEquiv (.inl (i, 0)))) = part ((vertexEquiv (.inl (0, 0)))) := by simpa [rawTop] using ht
  exact hs'.trans ht'

private theorem large_part_eq {m : ℕ} (part : Fin 14 → Fin m)
    (hp : ∀ g ∈ G, ∀ v, part (g v) = part v) (i : Fin 2) (j : Fin 4) :
    part ((vertexEquiv (.inr (i, j)))) = part ((vertexEquiv (.inr (0, 0)))) := by
  have hs := hp _ (transported_mem (swap_mem (.inr (i, 0)) (.inr (i, j)) rfl))
    ((vertexEquiv (.inr (i, 0))))
  have hs' : part ((vertexEquiv (.inr (i, j)))) = part ((vertexEquiv (.inr (i, 0)))) := by simpa [] using hs
  have ht := hp _ (transported_mem (rawTop_mem (Equiv.swap 0 1))) ((vertexEquiv (.inr (0, 0))))
  have ht' : part ((vertexEquiv (.inr (1, 0)))) = part ((vertexEquiv (.inr (0, 0)))) := by
    simpa [rawTop, parityAct,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1)] using ht
  fin_cases i
  · exact hs'
  · exact hs'.trans ht'

private theorem layer_labels_distinct {m : ℕ} (hm : 2 ≤ m) (part : Fin 14 → Fin m)
    (hs : Function.Surjective part)
    (hp : ∀ g ∈ G, ∀ v, part (g v) = part v) :
    part ((vertexEquiv (.inl (0, 0)))) ≠ part ((vertexEquiv (.inr (0, 0)))) := by
  intro heq
  have hc : ∀ v, part v = part ((vertexEquiv (.inl (0, 0)))) := by
    intro v
    obtain ⟨w, rfl⟩ := vertexEquiv.surjective v
    cases w with
    | inl q => exact small_part_eq part hp q.1 q.2
    | inr q => exact (large_part_eq part hp q.1 q.2).trans heq.symm
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  obtain ⟨u, hu⟩ := hs i0
  obtain ⟨v, hv⟩ := hs i1
  have hi : i0 = i1 := hu.symm.trans ((hc u).trans ((hc v).symm.trans hv))
  have hbad := congrArg Fin.val hi
  change 0 = 1 at hbad
  omega

private theorem supported_even {m : ℕ} (hm : 2 ≤ m) (part : Fin 14 → Fin m)
    (hs : Function.Surjective part)
    (hp : ∀ g ∈ G, ∀ v, part (g v) = part v)
    (i : Fin m) (g : Equiv.Perm (Fin 14)) (hg : g ∈ G)
    (hf : ∀ v, part v ≠ i → g v = v) : g ∈ evenG := by
  obtain ⟨t, ht, rfl⟩ := hg
  by_cases hi : i = part ((vertexEquiv (.inl (0, 0))))
  · have hfix : ∀ b k, t (.inr (b, k)) = .inr (b, k) := by
      intro b k
      apply vertexEquiv.injective
      have hx := hf ((vertexEquiv (.inr (b, k)))) (by
        rw [large_part_eq part hp b k, hi]
        exact (layer_labels_distinct hm part hs hp).symm)
      simpa [] using hx
    exact Subgroup.mem_map_of_mem _ (fixes_large_even ht hfix)
  · have hfix : ∀ b k, t (.inl (b, k)) = .inl (b, k) := by
      intro b k
      apply vertexEquiv.injective
      have hx := hf ((vertexEquiv (.inl (b, k)))) (by rw [small_part_eq part hp b k]; exact Ne.symm hi)
      simpa [] using hx
    exact Subgroup.mem_map_of_mem _ (fixes_small_even ht hfix)

private theorem no_product_parts {m : ℕ} (hm : 2 ≤ m) (part : Fin 14 → Fin m)
    (hs : Function.Surjective part) :
    ¬ (∃ Gi : Fin m → Subgroup (Equiv.Perm (Fin 14)),
      (∀ i, Gi i ≤ G) ∧
      (∀ i g, g ∈ Gi i → ∀ v, part v ≠ i → g v = v) ∧
      Subgroup.closure (⋃ i, (Gi i : Set (Equiv.Perm (Fin 14)))) = G) := by
  rintro ⟨Gi, hGi, hf, hgen⟩
  have hp := generated_preserves part Gi hf hgen
  have hsub : Subgroup.closure (⋃ i, (Gi i : Set (Equiv.Perm (Fin 14)))) ≤ evenG := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact supported_even hm part hs hp i g (hGi i hi) (hf i g hi)
  rw [hgen] at hsub
  exact odd_top_not_even (hsub (transported_mem (rawTop_mem (Equiv.swap 0 1))))


private theorem irreducible : IsIrreducible graph G := by
  rintro ⟨m, hm, part, hs, he, hred⟩
  rcases hred with hprod | hiso
  · exact no_product_parts hm part hs hprod
  · exact no_isomorphic_parts hm part hs he hiso


private theorem even_top_cube : ∀ h : Equiv.Perm (Fin 3),
    Equiv.Perm.sign h = 1 → h ^ 3 = 1 := by decide

private theorem odd_top_square : ∀ h : Equiv.Perm (Fin 3),
    Equiv.Perm.sign h ≠ 1 → h ^ 2 = 1 := by decide

private theorem odd_top_moved : ∀ h : Equiv.Perm (Fin 3),
    Equiv.Perm.sign h ≠ 1 →
    (Finset.univ.filter fun v : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)) => topHom h (blockW v) ≠ blockW v).card = 12 := by
  decide

private theorem block_colouring_injective {c : ℕ} (f : Fin 14 → Fin c)
    (hf : ∀ u v, graph.Adj u v → f u ≠ f v) (v w : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)))
    (hb : blockW v = blockW w) (he : f (vertexEquiv v) = f (vertexEquiv w)) : v = w := by
  by_contra hn
  have hadj : graph.Adj (vertexEquiv v) (vertexEquiv w) :=
    ⟨fun h => hn (vertexEquiv.injective h), not_ne_iff.mpr (by simpa [Function.comp_def] using hb)⟩
  exact hf _ _ hadj he

private theorem proper_fixed_sign {c : ℕ} (f : Fin 14 → Fin c)
    (hf : ∀ u v, graph.Adj u v → f u ≠ f v)
    (g : Equiv.Perm (Fin 14)) (hg : g ∈ G)
    (hfixed : ∀ v, f (g v) = f v) : Equiv.Perm.sign g = 1 := by
  obtain ⟨t, ⟨h, hb⟩, rfl⟩ := hg
  have hfix : ∀ v, f (vertexEquiv (t v)) = f (vertexEquiv v) := by
    intro v
    simpa using hfixed (vertexEquiv v)
  have hpfix : ∀ n v, f (vertexEquiv ((t ^ n) v)) = f (vertexEquiv v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; simpa [pow_succ', Equiv.Perm.mul_apply, hfix] using ih v
  have hpblock : ∀ n v, blockW ((t ^ n) v) = topHom (h ^ n) (blockW v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih => intro v; simp only [pow_succ', Equiv.Perm.mul_apply, hb, ih, map_mul]
  have hp : ∀ n, h ^ n = 1 → t ^ n = 1 := by
    intro n hn
    apply Equiv.ext
    intro v
    apply block_colouring_injective f hf
    · simpa [hn] using hpblock n v
    · exact hpfix n v
  have hsign : Equiv.Perm.sign t = 1 := by
    by_cases hh : Equiv.Perm.sign h = 1
    · have ht := hp 3 (even_top_cube h hh)
      have hs := congrArg Equiv.Perm.sign ht
      rcases Int.units_eq_one_or (Equiv.Perm.sign t) with he | he
      · exact he
      · have hn : (-1 : ℤˣ) ^ 3 ≠ 1 := by decide
        exact False.elim (hn (by simpa [he] using hs))
    · have ht := hp 2 (odd_top_square h hh)
      have hsupp : t.support = Finset.univ.filter
          (fun v : ((Fin 3 × Fin 2) ⊕ (Fin 2 × Fin 4)) => topHom h (blockW v) ≠ blockW v) := by
        ext v
        simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hv he
          apply hv
          exact block_colouring_injective f hf (t v) v (by rw [hb, he]) (hfix v)
        · intro hv he
          exact hv (by rw [← hb, he])
      have hc : t.support.card = 12 := by rw [hsupp]; exact odd_top_moved h hh
      have hfp := Equiv.Perm.card_fixedPoints t
      have hsum := Equiv.Perm.sum_cycleType t
      rw [hsum, hc] at hfp
      have hzero : Fintype.card (Function.fixedPoints t) = 2 := by
        simpa [Fintype.card_sum, Fintype.card_prod] using hfp
      rw [Equiv.Perm.sign_of_pow_two_eq_one ht, hzero]
      norm_num
      decide
  simpa [Equiv.permCongrHom_coe] using
    (Equiv.Perm.sign_permCongr vertexEquiv t).trans hsign


private def cycleTag (g : Equiv.Perm V) (v : V) :
    Function.fixedPoints g ⊕ (g.cycleFactorsFinset : Set (Equiv.Perm V)) := by
  classical
  exact if hv : g v = v then .inl ⟨v, hv⟩
    else .inr ⟨g.cycleOf v,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr hv)⟩

private theorem cycleTag_eq_iff (g : Equiv.Perm V) (v w : V) :
    cycleTag g v = cycleTag g w ↔ g.SameCycle v w := by
  classical
  by_cases hv : g v = v <;> by_cases hw : g w = w
  · constructor
    · intro ht
      have e : (⟨v, hv⟩ : Function.fixedPoints g) = ⟨w, hw⟩ := by
        simpa [cycleTag, hv, hw] using ht
      have h : v = w := congrArg Subtype.val e
      subst w
      exact Equiv.Perm.SameCycle.refl g v
    · intro h
      have e : v = w := h.eq_of_left hv
      subst w
      rfl
  · simp only [cycleTag, hv, hw, dite_true, dite_false, Sum.inl_ne_inr, false_iff]
    intro h
    exact hw (h.apply_eq_self_iff.mp hv)
  · simp only [cycleTag, hv, hw, dite_true, dite_false, Sum.inr_ne_inl, false_iff]
    intro h
    exact hv (h.apply_eq_self_iff.mpr hw)
  · simp only [cycleTag, hv, hw, dite_false, Sum.inr.injEq, Subtype.mk.injEq]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr hv) (Equiv.Perm.mem_support.mpr hw)).symm

private theorem cycleTag_surjective (g : Equiv.Perm V) : Function.Surjective (cycleTag g) := by
  classical
  intro q
  cases q with
  | inl v =>
    have hv : g v.val = v.val := v.prop
    exact ⟨v.val, by simp [cycleTag, hv]⟩
  | inr c =>
    obtain ⟨v, hv⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support
    have hg : g v ≠ v := Equiv.Perm.mem_support.mp
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hv)
    have hc : g.cycleOf v = c.val := (Equiv.Perm.cycle_is_cycleOf hv c.prop).symm
    exact ⟨v, by simp [cycleTag, hg, hc]⟩

private theorem cycleCount_eq (g : Equiv.Perm V) :
    actualCycleCount g = Fintype.card (Function.fixedPoints g) + g.cycleType.card := by
  classical
  let tag : Quotient (Equiv.Perm.SameCycle.setoid g) →
      Function.fixedPoints g ⊕ (g.cycleFactorsFinset : Set (Equiv.Perm V)) :=
    Quotient.lift (cycleTag g) (fun v w h => (cycleTag_eq_iff g v w).mpr h)
  have hi : Function.Injective tag := by
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro v w h
    exact Quotient.sound ((cycleTag_eq_iff g v w).mp h)
  have hs : Function.Surjective tag := by
    intro q
    obtain ⟨v, hv⟩ := cycleTag_surjective g q
    exact ⟨Quotient.mk _ v, hv⟩
  have h := Fintype.card_congr (Equiv.ofBijective tag ⟨hi, hs⟩)
  simpa [actualCycleCount, Nat.card_eq_fintype_card, Equiv.Perm.cycleType] using h

private theorem sign_cycleCount (g : Equiv.Perm V) :
    (Equiv.Perm.sign g : ℤ) = (-1 : ℤ) ^ (Fintype.card V + actualCycleCount g) := by
  classical
  have hf := Equiv.Perm.card_fixedPoints g
  have hle := Equiv.Perm.sum_cycleType_le g
  have he : Fintype.card V + actualCycleCount g =
      g.cycleType.sum + g.cycleType.card + 2 * Fintype.card (Function.fixedPoints g) := by
    rw [cycleCount_eq]
    omega
  rw [he]
  have h := congrArg (fun u : ℤˣ => (u : ℤ)) (Equiv.Perm.sign_of_cycleType g)
  simpa [pow_add, pow_mul] using h


private def allFixed (g : Equiv.Perm V) (c : ℕ) : Finset (V → Fin c) := by
  classical
  exact Finset.univ.filter (fun f => ∀ v, f (g v) = f v)

omit [Fintype V] [DecidableEq V] in
private theorem fixed_sameCycle [Finite V] {B : Type*} (g : Equiv.Perm V) (f : V → B)
    (hf : ∀ v, f (g v) = f v) {v w : V} (h : g.SameCycle v w) : f v = f w := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have hi := (show Function.Semiconj f g id from hf).iterate_right n v
  have hp : f ((g ^ n) v) = f v := by
    simpa only [Equiv.Perm.coe_pow, Function.iterate_id, id_eq] using hi
  exact (hn ▸ hp).symm

private theorem allFixed_card (g : Equiv.Perm V) (c : ℕ) :
    (allFixed g c).card = c ^ actualCycleCount g := by
  classical
  have e : {f : V → Fin c // ∀ v, f (g v) = f v} ≃
      {f : V → Fin c // Equiv.Perm.SameCycle.setoid g ≤ Setoid.ker f} :=
    Equiv.subtypeEquivRight (fun f => ⟨
      fun hf _ _ h => fixed_sameCycle g f hf h,
      fun hf v => hf (Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.SameCycle.refl g v)).symm⟩)
  have h := Fintype.card_congr (e.trans (Setoid.liftEquiv (Equiv.Perm.SameCycle.setoid g)))
  simpa [Fintype.subtype_card, allFixed, Fintype.card_fun, actualCycleCount, Nat.card_eq_fintype_card] using h


private theorem signed_indicator_cancel {T : Type*} [Group T] [Fintype T]
    (χ : T →* ℤˣ) (P : T → Prop) [DecidablePred P] (t : T)
    (ht : χ t = -1) (hP : ∀ g, P (t * g) ↔ P g) :
    (∑ g : T, if P g then (χ g : ℤ) else 0) = 0 := by
  classical
  let a : T → ℤ := fun g => if P g then (χ g : ℤ) else 0
  have ha : ∀ g, a (t * g) = -a g := by
    intro g
    by_cases hp : P g <;> simp [a, hP, hp, map_mul, ht]
  have hsum : (∑ g, a g) = -(∑ g, a g) := by
    calc
      (∑ g, a g) = ∑ g, a (t * g) := (Equiv.sum_comp (Equiv.mulLeft t) a).symm
      _ = ∑ g, -a g := Finset.sum_congr rfl (fun g _ => ha g)
      _ = -(∑ g, a g) := Finset.sum_neg_distrib a
  change (∑ g, a g) = 0
  omega


private theorem filter_card_int {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    (((Finset.univ.filter P).card : ℕ) : ℤ) =
      ∑ a : A, if P a then (1 : ℤ) else 0 := by
  exact Finset.natCast_card_filter P Finset.univ

private theorem signed_colour_sum (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (G : Subgroup (Equiv.Perm V)) [Fintype G]
    (hswap : ∀ u v, Γ.Adj u v → Equiv.swap u v ∈ G)
    (hpos : ∀ c (f : V → Fin c),
      (∀ u v, Γ.Adj u v → f u ≠ f v) →
      ∀ g ∈ G, (∀ v, f (g v) = f v) → Equiv.Perm.sign g = 1)
    (c : ℕ) (f : V → Fin c) :
    (∑ g : G, if ∀ v, f ((g : Equiv.Perm V) v) = f v
      then (Equiv.Perm.sign (g : Equiv.Perm V) : ℤ) else 0) =
    ∑ g : G, if (∀ u v, Γ.Adj u v → f u ≠ f v) ∧
      (∀ v, f ((g : Equiv.Perm V) v) = f v) then (1 : ℤ) else 0 := by
  classical
  by_cases hp : ∀ u v, Γ.Adj u v → f u ≠ f v
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : ∀ v, f ((g : Equiv.Perm V) v) = f v
    · rw [if_pos hg, if_pos ⟨hp, hg⟩, hpos c f hp g g.prop hg]
      rfl
    · simp [hg]
  · obtain ⟨u, v, huv, heq⟩ :=
      (show ∃ u v, Γ.Adj u v ∧ f u = f v from by
        simpa only [not_forall, Classical.not_imp, not_not, exists_prop] using hp)
    let t : G := ⟨Equiv.swap u v, hswap u v huv⟩
    have ht : (Equiv.Perm.sign.comp G.subtype) t = -1 :=
      Equiv.Perm.sign_swap (Γ.ne_of_adj huv)
    have hfixed := swap_fixed f u v heq
    have hP : ∀ g : G,
        (∀ w, f (((t * g : G) : Equiv.Perm V) w) = f w) ↔
        (∀ w, f ((g : Equiv.Perm V) w) = f w) := by
      intro g
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
      change (∀ w, f (Equiv.swap u v ((g : Equiv.Perm V) w)) = f w) ↔ _
      simp only [hfixed]
    have hz := signed_indicator_cancel (Equiv.Perm.sign.comp G.subtype)
      (fun g : G => ∀ w, f ((g : Equiv.Perm V) w) = f w) t ht hP
    simpa [hp] using hz


omit [DecidableEq V] in
open scoped Classical in
private theorem cycleConvention (g : Equiv.Perm V) :
    Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid g)) = actualCycleCount g := by
  classical
  simp only [actualCycleCount, Nat.card_eq_fintype_card]

private theorem signed_cycle_total (G : Subgroup (Equiv.Perm V)) [Fintype G] (c : ℕ) :
    (-1 : ℤ) ^ Fintype.card V * (cyclePoly G).eval (-(c : ℤ)) =
      ∑ g : G, (Equiv.Perm.sign (g : Equiv.Perm V) : ℤ) *
        ((allFixed (g : Equiv.Perm V) c).card : ℤ) := by
  classical
  rw [cyclePoly, Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Polynomial.eval_X_pow, cycleConvention, allFixed_card, Nat.cast_pow, sign_cycleCount, pow_add]
  rw [show -(c : ℤ) = (-1 : ℤ) * (c : ℤ) by ring, mul_pow]
  ring

private theorem reciprocal_of_signed_counting (Γ : SimpleGraph V)
    (G : Subgroup (Equiv.Perm V)) [Fintype G]
    (hswap : ∀ u v, Γ.Adj u v → Equiv.swap u v ∈ G)
    (hpos : ∀ c (f : V → Fin c),
      (∀ u v, Γ.Adj u v → f u ≠ f v) →
      ∀ g ∈ G, (∀ v, f (g v) = f v) → Equiv.Perm.sign g = 1) :
    IsReciprocal Γ G := by
  classical
  intro c _
  have hcard :
      ((∑ g : G, (fixedColourings Γ g c).card : ℕ) : ℤ) =
      ∑ g : G, ∑ f : V → Fin c,
        if (∀ u v, Γ.Adj u v → f u ≠ f v) ∧
          (∀ v, f ((g : Equiv.Perm V) v) = f v) then (1 : ℤ) else 0 := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro g _
    simp [fixedColourings]
  have hsigncard :
      (∑ g : G, (Equiv.Perm.sign (g : Equiv.Perm V) : ℤ) *
        ((allFixed (g : Equiv.Perm V) c).card : ℤ)) =
      ∑ g : G, ∑ f : V → Fin c,
        if ∀ v, f ((g : Equiv.Perm V) v) = f v
          then (Equiv.Perm.sign (g : Equiv.Perm V) : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro g _
    have h := filter_card_int (fun f : V → Fin c => ∀ v, f ((g : Equiv.Perm V) v) = f v)
    unfold allFixed
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> simp
  rw [hcard, signed_cycle_total, hsigncard]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  exact (signed_colour_sum Γ G hswap hpos c f).symm


private theorem edge_swap_mem (u v : Fin 14) (ha : graph.Adj u v) : Equiv.swap u v ∈ G := by
  have hm := transported_mem (swap_mem (vertexEquiv.symm u) (vertexEquiv.symm v) (not_ne_iff.mp ha.2))
  have heq : vertexEquiv.permCongrHom
      (Equiv.swap (vertexEquiv.symm u) (vertexEquiv.symm v)) = Equiv.swap u v := by
    simpa only [Equiv.permCongrHom_coe, Equiv.permCongr_def, Equiv.apply_symm_apply] using
      (Equiv.symm_trans_swap_trans (vertexEquiv.symm u) (vertexEquiv.symm v) vertexEquiv)
  rwa [heq] at hm

open scoped Classical in
private theorem reciprocal : IsReciprocal graph G :=
  reciprocal_of_signed_counting graph G edge_swap_mem
    (fun _ f hf g hg hfix => proper_fixed_sign f hf g hg hfix)

theorem result : ¬ claim := by
  classical
  intro h
  exact not_listed (h (Fin 14) graph G group_aut reciprocal irreducible)

end D5.S3.Combinatorics.ReciprocalPairs.GroupGraphReciprocalRefutation
