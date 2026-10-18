/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindowProducts
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindowProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint constant blocks factor and give the three exact path-extension probabilities. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SpinWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

namespace FiniteSpinLaw

variable {ι : Type*} [Fintype ι]

theorem two_constant_mass (β : Bias) (A B : Finset ι) (hd : Disjoint A B) (s t : Bool) :
    mass β ({σ | ∀ i ∈ A, σ i = s} ∩ {σ | ∀ i ∈ B, σ i = t}) =
      (β.π s)^A.card * (β.π t)^B.card := by
  have he : ({σ : ι → Bool | ∀ i ∈ A, σ i = s} ∩ {σ | ∀ i ∈ B, σ i = t}) =
      {σ | ∀ i ∈ A ∪ B, σ i = if i ∈ A then s else t} := by
    ext σ
    constructor
    · rintro ⟨hA, hB⟩ i hi
      by_cases hia : i ∈ A
      · simp [hia, hA i hia]
      · have hib : i ∈ B := (Finset.mem_union.mp hi).resolve_left hia
        simp [hia, hB i hib]
    · intro h
      constructor
      · intro i hi; simpa [hi] using h i (Finset.mem_union_left _ hi)
      · intro i hi
        have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
        simpa [hn] using h i (Finset.mem_union_right _ hi)
  rw [he, prescribed_mass, Finset.prod_union hd]
  have hA : (∏ i ∈ A, β.π (if i ∈ A then s else t)) = (β.π s)^A.card := by
    calc
      _ = ∏ _ ∈ A, β.π s := Finset.prod_congr rfl fun i hi => by simp [hi]
      _ = _ := by simp
  have hB : (∏ i ∈ B, β.π (if i ∈ A then s else t)) = (β.π t)^B.card := by
    calc
      _ = ∏ _ ∈ B, β.π t := Finset.prod_congr rfl fun i hi => by
        have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
        simp [hn]
      _ = _ := by simp
  rw [hA, hB]

end FiniteSpinLaw

namespace SpinWindow

theorem two_constant_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B) (s t : Bool) :
    prob β V (constant A s ∩ constant B t) =
      (β.π s)^A.card * (β.π t)^B.card := by
  have he (C : Finset ℤ) (hC : C ⊆ V) (u : Bool) :
      {σ : V → Bool | extend V σ ∈ constant C u} =
        {σ | ∀ i ∈ C.subtype (· ∈ V), σ i = u} := by
    ext σ
    constructor
    · intro h i hi
      have hi' : i.val ∈ C := Finset.mem_subtype.mp hi
      simpa only [extend_apply V σ i.val i.property] using h i.val hi'
    · intro h i hi
      have hiV := hC hi
      simpa only [extend_apply V σ i hiV] using
        h ⟨i, hiV⟩ (Finset.mem_subtype.mpr hi)
  have hd' : Disjoint (A.subtype (· ∈ V)) (B.subtype (· ∈ V)) := by
    apply Finset.disjoint_left.mpr
    intro i ha hb
    exact Finset.disjoint_left.mp hd (Finset.mem_subtype.mp ha) (Finset.mem_subtype.mp hb)
  change FiniteSpinLaw.mass β
    ({σ | extend V σ ∈ constant A s} ∩ {σ | extend V σ ∈ constant B t}) = _
  rw [he A hA s, he B hB t, FiniteSpinLaw.two_constant_mass β _ _ hd',
    Finset.card_subtype, Finset.card_subtype,
    Finset.filter_eq_self.mpr hA, Finset.filter_eq_self.mpr hB]

theorem block_constant_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B) (hne : A.Nonempty) (s : Bool) :
    prob β V (monoBlock A ∩ constant B s) = β.T A.card * (β.π s)^B.card := by
  have he : monoBlock A ∩ constant B s =
      (constant A false ∩ constant B s) ∪ (constant A true ∩ constant B s) := by
    ext S; simp only [monoBlock, Set.mem_inter_iff, Set.mem_union]; tauto
  have hdis : Disjoint (constant A false ∩ constant B s)
      (constant A true ∩ constant B s) := by
    apply Set.disjoint_left.mpr
    intro S h0 h1
    exact Set.disjoint_left.mp (constant_disjoint A hne) h0.1 h1.1
  rw [he, prob_union β V hdis, two_constant_prob β V A B hA hB hd,
    two_constant_prob β V A B hA hB hd]
  simp only [Bias.T, Bias.π, Bool.false_eq_true, ↓reduceIte]
  ring

theorem two_blocks_prob (β : Bias) (V A B : Finset ℤ)
    (hA : A ⊆ V) (hB : B ⊆ V) (hd : Disjoint A B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    prob β V (monoBlock A ∩ monoBlock B) = β.T A.card * β.T B.card := by
  have he : monoBlock A ∩ monoBlock B =
      (monoBlock A ∩ constant B false) ∪ (monoBlock A ∩ constant B true) := by
    ext S; simp only [monoBlock, Set.mem_inter_iff, Set.mem_union]; tauto
  have hdis : Disjoint (monoBlock A ∩ constant B false)
      (monoBlock A ∩ constant B true) := by
    apply Set.disjoint_left.mpr
    intro S h0 h1
    exact Set.disjoint_left.mp (constant_disjoint B hneB) h0.2 h1.2
  rw [he, prob_union β V hdis, block_constant_prob β V A B hA hB hd hneA,
    block_constant_prob β V A B hA hB hd hneA]
  simp only [Bias.T, Bias.π, Bool.false_eq_true, ↓reduceIte]
  ring

theorem zero_insert (E : Finset ℤ) (e : ℤ) :
    zeroEdges (insert e E) = zeroEdges E ∩ {S | S e = S (e + 1)} := by
  ext S; simp only [zeroEdges, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.forall_mem_insert]; tauto

theorem pair_zero_eq_block (e : ℤ) :
    {S : Spins | S e = S (e + 1)} = monoBlock {e, e + 1} := by
  ext S
  simp only [monoBlock, constant, Set.mem_union, Set.mem_setOf_eq, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq]
  cases h0 : S e <;> cases h1 : S (e + 1) <;> simp [h0, h1]

theorem repeated_edge_prob (β : Bias) (V : Finset ℤ) (L e : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (he : e ∈ pathEdges L n) :
    prob β V (zeroEdges (insert e (pathEdges L n))) = β.T (n + 1) := by
  rw [Finset.insert_eq_of_mem he, zero_path_prob β V L n hV]

theorem separated_edge_prob (β : Bias) (V : Finset ℤ) (L e : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (heV : {e, e + 1} ⊆ V)
    (hd : Disjoint ({e, e + 1} : Finset ℤ) (pathVertices L n)) :
    prob β V (zeroEdges (insert e (pathEdges L n))) = β.T 2 * β.T (n + 1) := by
  rw [zero_insert, zero_path_eq_block, pair_zero_eq_block,
    two_blocks_prob β V _ _ hV heV hd.symm
      ⟨L, by simp [pathVertices]⟩ ⟨e, by simp⟩, vertices_card]
  have hc : ({e, e + 1} : Finset ℤ).card = 2 := by simp
  rw [hc, mul_comm]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
