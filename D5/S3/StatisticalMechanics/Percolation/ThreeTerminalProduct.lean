/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent network substitution preserves all five terminal partition masses. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalTriangleArms

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalGluing
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

/-- Detach the third label when the independent connecting network is closed. -/
def detachThird (s : Mode) (b : Bool) : Mode :=
  if b then s else match s with
    | .all | .ab => .ab
    | _ => .separate

private lemma independent_detach {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Mode) (Q : Y → Bool) (w : X → ℝ) (v : Y → ℝ)
    (hv : ∑ y, v y = 1) (s : Mode) :
    let p := fun t => ∑ x, if P x = t then w x else 0
    let q := ∑ y, if Q y then v y else 0
    (∑ x, ∑ y, if detachThird (P x) (Q y) = s then w x * v y else 0) =
      match s with
      | .all => q*p .all
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .ac => q*p .ac
      | .separate => p .separate+(1-q)*(p .bc+p .ac) := by
  classical
  dsimp only
  have hfalse : (∑ y, if Q y then 0 else v y) =
      1-(∑ y, if Q y then v y else 0) := by
    have hh : (∑ y, if Q y then v y else 0)+(∑ y, if Q y then 0 else v y) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hv using 1
      apply Finset.sum_congr rfl
      intro y _
      cases Q y <;> simp
    linarith
  have hsplit (x : X) (y : Y) :
      (if detachThird (P x) (Q y) = s then w x*v y else 0) =
        (if P x = s then w x else 0)*(if Q y then v y else 0)+
        (if detachThird (P x) false = s then w x else 0)*(if Q y then 0 else v y) := by
    cases hQ : Q y <;> simp only [detachThird,hQ,Bool.false_eq_true,if_false,if_true]
    all_goals split_ifs <;> ring
  simp_rw [hsplit,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.sum_mul,hfalse]
  have hlast : (∑ x, if detachThird (P x) false = s then w x else 0) =
      match s with
      | .ab => (∑ x, if P x = .ab then w x else 0)+(∑ x, if P x = .all then w x else 0)
      | .separate => (∑ x, if P x = .separate then w x else 0)+
          (∑ x, if P x = .bc then w x else 0)+(∑ x, if P x = .ac then w x else 0)
      | _ => 0 := by
    cases s <;> simp only [← Finset.sum_add_distrib]
    all_goals try { rw [← Finset.sum_const_zero] }
    all_goals apply Finset.sum_congr rfl
    all_goals intro x _; cases P x <;> simp [detachThird]
  rw [hlast]
  cases s <;> dsimp only <;> ring

private lemma openGraph_sum {V E F : Type*} (e : E → V × V) (f : F → V × V)
    (ω : E → Bool) (η : F → Bool) :
    openGraph (Sum.elim e f) (Sum.elim ω η) = openGraph e ω ⊔ openGraph f η := by
  ext x y
  simp only [openGraph,SimpleGraph.fromRel_adj,SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hne,h | h⟩
    all_goals obtain ⟨i,hi,he⟩ := h
    all_goals cases i with
      | inl i => exact Or.inl ⟨hne,by aesop⟩
      | inr i => exact Or.inr ⟨hne,by aesop⟩
  · rintro (⟨hne,h | h⟩ | ⟨hne,h | h⟩)
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inl ⟨Sum.inl i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inr ⟨Sum.inl i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inl ⟨Sum.inr i,hi,he⟩⟩
    · obtain ⟨i,hi,he⟩ := h
      exact ⟨hne,Or.inr ⟨Sum.inr i,hi,he⟩⟩

private lemma openGraph_le_full {V E : Type*} (e : E → V × V) (ω : E → Bool) :
    openGraph e ω ≤ openGraph e (fun _ => true) := by
  intro x y h
  simp only [openGraph,SimpleGraph.fromRel_adj] at h ⊢
  aesop

private lemma partition_graphMode {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (e : E → V × V) (a b c : V) (ω : E → Bool) :
    partition e a b c ω = graphMode (openGraph e ω) a b c := by
  classical
  simp [partition,connected,graphMode]

/-- The reliability is computed on the complete edge cube of the attached
network, including configurations of edges irrelevant to the connection. -/
def reliability {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F]
    (f : F → V × V) (g c : V) (ρ : F → ℝ) : ℝ :=
  ∑ η : F → Bool, if connected f η g c then weight ρ η else 0

/-- Joining two independent edge networks at a single gate transforms all five
partition probabilities together. No strict positivity or distinctness of the
terminals is needed. Both probability laws are finite sums on actual graphs. -/
theorem joined_network_law {V E F : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (e : E → V × V) (f : F → V × V) (A B : Set V) (a b c g : V)
    (h : OneVertexUnion (openGraph e (fun _ => true))
      (openGraph f (fun _ => true)) A B g)
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ B)
    (θ : E → ℝ) (ρ : F → ℝ) :
    let p := law e a b g θ
    let q := reliability f g c ρ
    law (Sum.elim e f) a b c (Sum.elim θ ρ) = fun s => match s with
      | .all => q*p .all
      | .ab => p .ab+(1-q)*p .all
      | .bc => q*p .bc
      | .ac => q*p .ac
      | .separate => p .separate+(1-q)*(p .bc+p .ac) := by
  classical
  have hpoint (ω : E → Bool) (η : F → Bool) :
      partition (Sum.elim e f) a b c (Sum.elim ω η) =
        detachThird (partition e a b g ω) (connected f η g c) := by
    rw [partition_graphMode,openGraph_sum]
    have h' : OneVertexUnion (openGraph e ω) (openGraph f η) A B g :=
      ⟨fun hxy => h.left_support (openGraph_le_full e ω hxy),
       fun hxy => h.right_support (openGraph_le_full f η hxy),h.intersection⟩
    rw [graphMode_pendant h' ha hb hc,partition_graphMode]
    simp only [detachThird,connected]
    split_ifs <;> rfl
  have hweight (ω : E → Bool) (η : F → Bool) :
      weight (Sum.elim θ ρ) (Sum.elim ω η) = weight θ ω * weight ρ η := by
    simp [weight,Fintype.prod_sum_type]
  funext s
  dsimp only
  unfold law
  rw [← (Equiv.sumArrowEquivProdArrow E F Bool).symm.sum_comp,Fintype.sum_prod_type]
  change (∑ ω : E → Bool, ∑ η : F → Bool,
    if partition (Sum.elim e f) a b c (Sum.elim ω η) = s
    then weight (Sum.elim θ ρ) (Sum.elim ω η) else 0) = _
  simp_rw [hpoint,hweight]
  exact independent_detach (partition e a b g) (fun η => connected f η g c)
    (weight θ) (weight ρ) (weight_sum ρ) s

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct
