/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindow
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SpinWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite integer spin windows compute constant blocks and target collision masses. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteSpinLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.IntegerPath

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
namespace SpinWindow

/-- The default outside a finite window is immaterial to events supported inside it. -/
def extend (V : Finset ℤ) (σ : V → Bool) : Spins :=
  fun i => if hi : i ∈ V then σ ⟨i, hi⟩ else false

@[simp] theorem extend_apply (V : Finset ℤ) (σ : V → Bool) (i : ℤ) (hi : i ∈ V) :
    extend V σ i = σ ⟨i, hi⟩ := dif_pos hi

def prob (β : Bias) (V : Finset ℤ) (E : Set Spins) : ℝ :=
  FiniteSpinLaw.mass β {σ | extend V σ ∈ E}

theorem prob_nonneg (β : Bias) (V : Finset ℤ) (E : Set Spins) : 0 ≤ prob β V E :=
  FiniteSpinLaw.mass_nonneg β _

@[simp] theorem prob_univ (β : Bias) (V : Finset ℤ) : prob β V Set.univ = 1 :=
  FiniteSpinLaw.mass_univ β

@[simp] theorem prob_empty (β : Bias) (V : Finset ℤ) : prob β V ∅ = 0 :=
  FiniteSpinLaw.mass_empty β

theorem prob_union (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : Disjoint E F) :
    prob β V (E ∪ F) = prob β V E + prob β V F := by
  apply FiniteSpinLaw.mass_union
  exact h.preimage _

theorem prob_diff (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : F ⊆ E) :
    prob β V (E \ F) = prob β V E - prob β V F :=
  FiniteSpinLaw.mass_diff β (fun _ hh => h hh)

theorem prob_mono (β : Bias) (V : Finset ℤ) {E F : Set Spins} (h : E ⊆ F) :
    prob β V E ≤ prob β V F := FiniteSpinLaw.mass_mono β (fun _ hh => h hh)

theorem prob_pos_iff (β : Bias) (V : Finset ℤ) (E : Set Spins) :
    0 < prob β V E ↔ ∃ σ : V → Bool, extend V σ ∈ E :=
  FiniteSpinLaw.mass_pos_iff β _

/-- Every actual finite configuration is retained by positive product weights. -/
theorem prob_one_iff (β : Bias) (V : Finset ℤ) (E : Set Spins) :
    prob β V E = 1 ↔ ∀ σ : V → Bool, extend V σ ∈ E := by
  rw [prob, FiniteSpinLaw.mass_one_iff]
  simp [Set.eq_univ_iff_forall]

def constant (A : Finset ℤ) (s : Bool) : Set Spins := {S | ∀ i ∈ A, S i = s}

def monoBlock (A : Finset ℤ) : Set Spins := constant A false ∪ constant A true

def zeroEdges (E : Finset ℤ) : Set Spins := {S | ∀ e ∈ E, S e = S (e + 1)}

theorem constant_prob (β : Bias) (V A : Finset ℤ) (hA : A ⊆ V) (s : Bool) :
    prob β V (constant A s) = (β.π s)^A.card := by
  have he : {σ : V → Bool | extend V σ ∈ constant A s} =
      {σ | ∀ i ∈ A.subtype (· ∈ V), σ i = s} := by
    ext σ
    constructor
    · intro h i hi
      have hi' : i.val ∈ A := Finset.mem_subtype.mp hi
      simpa only [extend_apply V σ i.val i.property] using h i.val hi'
    · intro h i hi
      have hiV := hA hi
      have hh := h ⟨i, hiV⟩ (Finset.mem_subtype.mpr hi)
      simpa only [extend_apply V σ i hiV] using hh
  unfold prob
  rw [he, FiniteSpinLaw.constant_mass, Finset.card_subtype,
    Finset.filter_eq_self.mpr hA]

theorem constant_disjoint (A : Finset ℤ) (hA : A.Nonempty) :
    Disjoint (constant A false) (constant A true) := by
  apply Set.disjoint_left.mpr
  intro S h0 h1
  obtain ⟨i, hi⟩ := hA
  have := (h0 i hi).symm.trans (h1 i hi)
  cases this

theorem monoBlock_prob (β : Bias) (V A : Finset ℤ) (hA : A ⊆ V) (hne : A.Nonempty) :
    prob β V (monoBlock A) = β.T A.card := by
  rw [monoBlock, prob_union β V (constant_disjoint A hne),
    constant_prob β V A hA, constant_prob β V A hA]
  rfl

theorem zero_path_eq_block (L : ℤ) (n : ℕ) :
    zeroEdges (pathEdges L n) = monoBlock (pathVertices L n) := by
  ext S
  change (∀ e ∈ pathEdges L n, S e = S (e + 1)) ↔
    (∀ v ∈ pathVertices L n, S v = false) ∨ (∀ v ∈ pathVertices L n, S v = true)
  rw [path_constant_iff]
  constructor
  · intro h
    cases hs : S L with
    | false => exact Or.inl (fun v hv => (h v hv).trans hs)
    | true => exact Or.inr (fun v hv => (h v hv).trans hs)
  · intro h v hv
    have hl : L ∈ pathVertices L n := by simp [pathVertices]
    rcases h with h | h <;> exact (h v hv).trans (h L hl).symm

theorem zero_path_prob (β : Bias) (V : Finset ℤ) (L : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) :
    prob β V (zeroEdges (pathEdges L n)) = β.T (n + 1) := by
  rw [zero_path_eq_block, monoBlock_prob β V _ hV, vertices_card]
  exact ⟨L, by simp [pathVertices]⟩

/-- The target section becomes a constant-spin block if the target lies on the path. -/
theorem target_collision_prob (β : Bias) (V : Finset ℤ) (L q : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (hq : q ∈ pathVertices L n) (s : Bool) :
    prob β V (zeroEdges (pathEdges L n) ∩ {S | S q = s}) = (β.π s)^(n + 1) := by
  have he : zeroEdges (pathEdges L n) ∩ {S | S q = s} = constant (pathVertices L n) s := by
    ext S
    exact path_target_iff L q n S s hq
  rw [he, constant_prob β V _ hV, vertices_card]

theorem target_collision_conditional (β : Bias) (V : Finset ℤ) (L q : ℤ) (n : ℕ)
    (hV : pathVertices L n ⊆ V) (hq : q ∈ pathVertices L n) (s : Bool) :
    prob β V (zeroEdges (pathEdges L n) ∩ {S | S q = s}) / β.π s = (β.π s)^n := by
  rw [target_collision_prob β V L q n hV hq s, pow_succ,
    mul_div_cancel_right₀ _ (ne_of_gt (β.π_pos s))]

end SpinWindow
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
