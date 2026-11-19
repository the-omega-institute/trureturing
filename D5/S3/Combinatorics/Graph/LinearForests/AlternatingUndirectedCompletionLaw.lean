/- GID: D5/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/AlternatingUndirectedCompletionLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Count actual alternating undirected cycles and condition on the inclusion of a fixed graph. -/

import D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
import D5.S3.Combinatorics.Graph.LinearForests.AlternatingCompletionLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw

open SimpleGraph Equiv
open CompatibleCycleInventory
open AlternatingCompletionLaw (ambient_card)
open D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] {F : SimpleGraph V}

private def graphAlternates (k : V → Bool) (C : SimpleGraph V) : Prop :=
  ∀ u v, C.Adj u v → k u ≠ k v

private def coloredForget (hn : 3 ≤ Fintype.card V) (k : V → Bool) :
    {l : Lift F // graphAlternates k (forget hn l).1} →
      {C : CompletedGraph F // graphAlternates k C.1} :=
  fun l => ⟨forget hn l.1, l.2⟩

private def coloredFiberEquiv (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (C : {C : CompletedGraph F // graphAlternates k C.1}) :
    { l // coloredForget hn k l = C } ≃ { l : Lift F // forget hn l = C.1 } where
  toFun l := ⟨l.1.1, congrArg Subtype.val l.2⟩
  invFun l := ⟨⟨l.1, l.2.symm ▸ C.2⟩, Subtype.ext l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def directedAlternatingPermutations (k : V → Bool) :=
  { σ : Equiv.Perm V // σ.IsCycleOn Set.univ ∧ ∀ x, k (σ x) ≠ k x }

private def coloredBotLiftEquiv (hn : 3 ≤ Fintype.card V) (k : V → Bool) :
    {l : Lift (⊥ : SimpleGraph V) // graphAlternates k (forget hn l).1} ≃
      directedAlternatingPermutations k := by
  let hcolor (l : Lift (⊥ : SimpleGraph V)) :
      (∀ x, k (l.σ x) ≠ k x) ↔ graphAlternates k (forget hn l).1 := by
    constructor
    · intro h x y hxy
      change (shadow l.σ).Adj x y at hxy
      rcases (shadow_adj
        hn l.σ l.full x y).mp hxy with he | he
      · simpa [he] using (h x).symm
      · simpa [he] using h y
    · intro h x
      apply (h x (l.σ x) ?_).symm
      exact (shadow_adj
        hn l.σ l.full x (l.σ x)).mpr (Or.inl rfl)
  let toLift (σ : directedAlternatingPermutations k) : Lift (⊥ : SimpleGraph V) :=
    { E := fun _ _ => False
      σ := σ.1
      edge := fun _ _ h => h.elim
      orient := fun _ _ h => h.elim
      antisymm := fun _ _ h => h.elim
      outgoing := fun _ _ _ h => h.elim
      incoming := fun _ _ _ h => h.elim
      full := σ.2.1
      extension := fun _ _ h => h.elim }
  refine {
    toFun := fun l => ⟨l.1.σ, l.1.full, (hcolor l.1).mpr l.2⟩
    invFun := fun σ => ⟨toLift σ, (hcolor (toLift σ)).mp σ.2.2⟩
    left_inv := fun l => Subtype.ext
      (lift_ext hn rfl)
    right_inv := fun _ => rfl }

/-- An actual undirected full cycle containing the prescribed graph and alternating the given colors. -/
abbrev AlternatingCompletedGraph (k : V → Bool) (F : SimpleGraph V) :=
  {C : CompletedGraph F // graphAlternates k C.1}

private abbrev ColoredLift (hn : 3 ≤ Fintype.card V) (k : V → Bool) (F : SimpleGraph V) :=
  {l : Lift F // graphAlternates k (forget hn l).1}

/-- Include a completion in the ambient space by forgetting its prescribed edges. -/
def forgetPrescribedEdges (k : V → Bool) (C : AlternatingCompletedGraph k F) :
    AlternatingCompletedGraph k (⊥ : SimpleGraph V) :=
  ⟨⟨C.1.1, C.1.2.1, C.1.2.2.1, bot_le⟩, C.2⟩

private def coloredCompletionEventEquiv (k : V → Bool) (F : SimpleGraph V) :
    {C : AlternatingCompletedGraph k (⊥ : SimpleGraph V) // F ≤ C.1.1} ≃ AlternatingCompletedGraph k F where
  toFun C := ⟨⟨C.1.1.1, C.1.1.2.1, C.1.1.2.2.1, C.2⟩, C.1.2⟩
  invFun C := ⟨forgetPrescribedEdges k C, C.1.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem colored_surjective (hn : 3 ≤ Fintype.card V) (k : V → Bool) :
    Function.Surjective (coloredForget hn (F := F) k) := by
  intro C
  obtain ⟨l, hl⟩ := forget_surjective hn F C.1
  exact ⟨⟨l, hl.symm ▸ C.2⟩, Subtype.ext hl⟩

private def directedCompatibleEquiv (hV : Nonempty V) (k : V → Bool) :
    directedAlternatingPermutations k ≃ Compatible k (fun x => !(k x)) where
  toFun σ := ⟨σ.1, hV, σ.2.1, fun x => Bool.not_eq_iff.mpr (σ.2.2 x).symm⟩
  invFun σ := ⟨σ.1, σ.2.2.1, fun x => (Bool.not_eq_iff.mp (σ.2.2.2 x)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem alternating_directed_card (hn : 3 ≤ Fintype.card V) (k : V → Bool)
    (n : ℕ) (hn' : 0 < n)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n) :
    Nat.card (ColoredLift hn k (⊥ : SimpleGraph V)) = n.factorial * (n - 1).factorial := by
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  rw [Nat.card_congr ((coloredBotLiftEquiv hn k).trans (directedCompatibleEquiv hV k))]
  exact ambient_card k n hn' hr hb

private theorem colored_card (hn : 3 ≤ Fintype.card V) (k : V → Bool) (F : SimpleGraph V) :
    Nat.card (ColoredLift hn k F) = 2 * Nat.card (AlternatingCompletedGraph k F) := by
  classical
  let : Finite (Lift F) := Finite.of_injective (fun l : Lift F => l.σ)
    (fun _ _ h => lift_ext hn h)
  let : Fintype (ColoredLift hn k F) := Fintype.ofFinite _
  let : Finite (AlternatingCompletedGraph k F) := Finite.of_surjective _ (colored_surjective hn k)
  let : Fintype (AlternatingCompletedGraph k F) := Fintype.ofFinite _
  let f : ColoredLift hn k F → AlternatingCompletedGraph k F := coloredForget hn k
  let (C : AlternatingCompletedGraph k F) : Fintype {l : ColoredLift hn k F // f l = C} := Fintype.ofFinite _
  have hc (C : AlternatingCompletedGraph k F) : Fintype.card {l : ColoredLift hn k F // f l = C} = 2 :=
    Nat.card_eq_fintype_card.symm.trans <|
      (Nat.card_congr (coloredFiberEquiv hn k C)).trans (forget_fiber_card hn C.1)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  simp [hc, Nat.mul_comm]

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf uniformPmf_toOuterMeasure_apply)
open scoped ENNReal

/-- Exact carrier size and fixed-edge conditioning for alternating undirected full cycles. -/
theorem alternating_undirected_completion_law (k : V → Bool) (F : SimpleGraph V)
    (n : ℕ) (hnColors : 2 ≤ n)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n) :
    let A := AlternatingCompletedGraph k (⊥ : SimpleGraph V)
    let S : Set A := {C | F ≤ C.1.1}
    let D := n.factorial * (n - 1).factorial / 2
    Nat.card A = D ∧ ∃ μ : PMF A,
      (∀ C, μ C = (D : ℝ≥0∞)⁻¹) ∧
      μ.toOuterMeasure S = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞) / D ∧
      (0 < μ.toOuterMeasure S ↔ Nonempty (AlternatingCompletedGraph k F)) ∧
      ∀ hs : ∃ C ∈ S, C ∈ μ.support,
        ∃ ν : PMF (AlternatingCompletedGraph k F),
          (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
          μ.filter S hs = ν.map (forgetPrescribedEdges k) := by
  classical
  dsimp only
  let A := AlternatingCompletedGraph k (⊥ : SimpleGraph V)
  let S : Set A := {C | F ≤ C.1.1}
  have hn : 3 ≤ Fintype.card V := by
    let : Fintype (Side k false) := Fintype.ofFinite _
    let : Fintype {x : V // ¬k x = false} := Fintype.ofFinite _
    have hred : Fintype.card (Side k false) = n :=
      Nat.card_eq_fintype_card.symm.trans hr
    have hblue : Fintype.card {x : V // ¬k x = false} = n := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.of_eq (Bool.not_eq_false (k x))))).trans hb
    have hsplit := Fintype.card_subtype_compl (fun x => k x = false)
    change Fintype.card {x : V // ¬k x = false} = Fintype.card V - Fintype.card (Side k false) at hsplit
    omega
  have hFold := colored_card hn k (⊥ : SimpleGraph V)
  rw [alternating_directed_card hn k n (by omega) hr hb] at hFold
  change n.factorial * (n - 1).factorial = 2 * Nat.card A at hFold
  have hD : Nat.card A = n.factorial * (n - 1).factorial / 2 := by omega
  have hpos : 0 < n.factorial * (n - 1).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  let : Finite (Lift (⊥ : SimpleGraph V)) := Finite.of_injective (fun l => l.σ)
    (fun _ _ h => lift_ext hn h)
  let : Finite A := Finite.of_surjective _ (colored_surjective hn k)
  let : Fintype A := Fintype.ofFinite A
  let : Nonempty A := Finite.card_pos_iff.mp (by omega : 0 < Nat.card A)
  let : Fintype S := Fintype.ofFinite S
  have hcardA : Fintype.card A = n.factorial * (n - 1).factorial / 2 :=
    Nat.card_eq_fintype_card.symm.trans hD
  have hcardS : Fintype.card S = Nat.card (AlternatingCompletedGraph k F) :=
    Nat.card_eq_fintype_card.symm.trans (Nat.card_congr (coloredCompletionEventEquiv k F))
  have hmass : (uniformPmf A).toOuterMeasure S =
      (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞) / (n.factorial * (n - 1).factorial / 2 : ℕ) := by
    rw [uniformPmf_toOuterMeasure_apply, hcardS, hcardA]
  let : Finite (Lift F) := Finite.of_injective (fun l => l.σ)
    (fun _ _ h => lift_ext hn h)
  let : Finite (AlternatingCompletedGraph k F) := Finite.of_surjective _ (colored_surjective hn k)
  refine ⟨hD, uniformPmf A, ?_, hmass, ?_, ?_⟩
  · simp [uniformPmf, hcardA]
  · change 0 < (uniformPmf A).toOuterMeasure S ↔ _
    have hInv : ((↑(n.factorial * (n - 1).factorial / 2 : ℕ)) : ℝ≥0∞)⁻¹ ≠ 0 :=
      (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)).ne'
    rw [hmass, div_eq_mul_inv, pos_iff_ne_zero, mul_ne_zero_iff]
    simp only [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finite.card_pos_iff]
    exact and_iff_left hInv
  · intro hs
    let : Nonempty S := by
      obtain ⟨C, hC, _⟩ := hs
      exact ⟨⟨C, hC⟩⟩
    let e : S ≃ AlternatingCompletedGraph k F := coloredCompletionEventEquiv k F
    let : Nonempty (AlternatingCompletedGraph k F) := Nonempty.map e ‹Nonempty S›
    let : Fintype (AlternatingCompletedGraph k F) := Fintype.ofFinite _
    refine ⟨uniformPmf _, ?_, ?_⟩
    · simp [uniformPmf, Nat.card_eq_fintype_card]
    · change (uniformPmf A).filter S hs = _
      have he := DirectedForestCompletion.uniform_equiv e.symm
      calc
        _ = (uniformPmf S).map Subtype.val :=
          @DirectedForestCompletion.uniform_filter
            A inferInstance inferInstance (fun C : A => F ≤ C.1.1)
              (inferInstance : Fintype S) (inferInstance : Nonempty S) hs
        _ = ((uniformPmf (AlternatingCompletedGraph k F)).map e.symm).map Subtype.val := by rw [he]
        _ = _ := by rw [PMF.map_comp]; rfl

end D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
