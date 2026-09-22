/- GID: D5/S3/Arith/Density/AsymptoticDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Density/AsymptoticDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Algebra.Order.LiminfLimsup, mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Upper and lower asymptotic densities of subsets of the naturals are defined by limsup and liminf, with upper-density subadditivity. -/

import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace D5.S3.Arith.Density.AsymptoticDensity

open Filter
open scoped Classical

noncomputable section

/-- The upper asymptotic density of a set of natural numbers, formed from the
limsup of its initial-segment counting ratios. -/
def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup
    (fun n : ℕ => (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) / (n : ℝ))
    Filter.atTop

/-- The lower asymptotic density of a set of natural numbers, formed from the
liminf of its initial-segment counting ratios. -/
def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf
    (fun n : ℕ => (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) / (n : ℝ))
    Filter.atTop

/-- A set has asymptotic density `d` when its lower and upper asymptotic
densities agree at `d`. -/
def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  lowerDensity A = upperDensity A ∧ upperDensity A = d

/-- Upper asymptotic density is subadditive under unions. -/
theorem upperDensity_union_le (A B : Set ℕ) :
    upperDensity (A ∪ B) ≤ upperDensity A + upperDensity B := by
  let f : ℕ → ℝ := fun n =>
    (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) / (n : ℝ)
  let g : ℕ → ℝ := fun n =>
    (((Finset.range n).filter (fun m => m ∈ B)).card : ℝ) / (n : ℝ)
  let h : ℕ → ℝ := fun n =>
    (((Finset.range n).filter (fun m => m ∈ A ∪ B)).card : ℝ) / (n : ℝ)
  have hnonnegf : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hnonnegg : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    positivity
  have hleonef : ∀ n, f n ≤ 1 := by
    intro n
    dsimp [f]
    by_cases hn : n = 0
    · simp [hn]
    · have hc : ((Finset.range n).filter (fun m => m ∈ A)).card ≤ n :=
        by simpa using Finset.card_filter_le (Finset.range n) (fun m => m ∈ A)
      have hcn : (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) ≤ n := by
        exact_mod_cast hc
      exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 (by simpa using hcn)
  have hleoneg : ∀ n, g n ≤ 1 := by
    intro n
    dsimp [g]
    by_cases hn : n = 0
    · simp [hn]
    · have hc : ((Finset.range n).filter (fun m => m ∈ B)).card ≤ n :=
        by simpa using Finset.card_filter_le (Finset.range n) (fun m => m ∈ B)
      have hcn : (((Finset.range n).filter (fun m => m ∈ B)).card : ℝ) ≤ n := by
        exact_mod_cast hc
      exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 (by simpa using hcn)
  have hpoint : ∀ n, h n ≤ f n + g n := by
    intro n
    dsimp [h, f, g]
    by_cases hn : n = 0
    · simp [hn]
    · have hcard :
          ((Finset.range n).filter (fun m => m ∈ A ∪ B)).card ≤
            ((Finset.range n).filter (fun m => m ∈ A)).card +
              ((Finset.range n).filter (fun m => m ∈ B)).card := by
        calc
          ((Finset.range n).filter (fun m => m ∈ A ∪ B)).card =
              (((Finset.range n).filter (fun m => m ∈ A)) ∪
                ((Finset.range n).filter (fun m => m ∈ B))).card := by
                congr 1
                simpa only [Set.mem_union] using
                  (Finset.filter_or (s := Finset.range n)
                    (p := fun m => m ∈ A) (q := fun m => m ∈ B))
          _ ≤ ((Finset.range n).filter (fun m => m ∈ A)).card +
                ((Finset.range n).filter (fun m => m ∈ B)).card :=
            Finset.card_union_le _ _
      have hcard' :
          (((Finset.range n).filter (fun m => m ∈ A ∪ B)).card : ℝ) ≤
            (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) +
              (((Finset.range n).filter (fun m => m ∈ B)).card : ℝ) := by
        exact_mod_cast hcard
      rw [div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]
      calc
        _ ≤ (((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) +
            (((Finset.range n).filter (fun m => m ∈ B)).card : ℝ) := hcard'
        _ = ((((Finset.range n).filter (fun m => m ∈ A)).card : ℝ) / (n : ℝ) +
            (((Finset.range n).filter (fun m => m ∈ B)).card : ℝ) / (n : ℝ)) * (n : ℝ) := by
          field_simp
  have hf_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop f :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => hleonef n)
  have hg_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop g :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => hleoneg n)
  have hf_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop f :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => hnonnegf n)
  have hg_lower : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop g :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => hnonnegg n)
  have hg_cobdd : IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop g :=
    hg_lower.isCoboundedUnder_le
  have hnonnegh : ∀ n, 0 ≤ h n := by
    intro n
    dsimp [h]
    positivity
  have hh_cobdd : IsCoboundedUnder (fun x y : ℝ => x ≤ y) atTop h :=
    isCoboundedUnder_le_of_le atTop (fun _ => hnonnegh _)
  have hfg_upper : IsBoundedUnder (fun x y : ℝ => x ≤ y) atTop (f + g) :=
    isBoundedUnder_le_add hf_upper hg_upper
  have hlim : Filter.limsup h atTop ≤ Filter.limsup (f + g) atTop := by
    apply limsup_le_limsup
    · exact Eventually.of_forall hpoint
    · exact hh_cobdd
    · exact hfg_upper
  calc
    upperDensity (A ∪ B) = Filter.limsup h atTop := by simp [upperDensity, h]
    _ ≤ Filter.limsup (f + g) atTop := hlim
    _ ≤ Filter.limsup f atTop + Filter.limsup g atTop := by
      apply limsup_add_le
      · exact hf_lower
      · exact hf_upper
      · exact hg_cobdd
      · exact hg_upper
    _ = upperDensity A + upperDensity B := by simp [upperDensity, f, g]

end

end D5.S3.Arith.Density.AsymptoticDensity
