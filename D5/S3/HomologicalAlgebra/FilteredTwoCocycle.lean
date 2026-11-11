/- GID: D5/S3/HomologicalAlgebra/FilteredTwoCocycle
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FilteredTwoCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree, mathlib/module/Mathlib.RepresentationTheory.Intertwining]
   utility: none
   digest: Pointwise lifting and correction propagate native two-cocycle triviality through exact sequences and finite stable filtrations. -/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose

/-!
Integration checkpoint pending the actual group-extension splitting consumer
and final admission. Native raw predicates use precisely the supplied
representation as their SMul instance. No coefficient section is assumed.
-/

set_option autoImplicit false

universe uR uG uA uB uC uM

namespace D5.S3.HomologicalAlgebra.FilteredTwoCocycle

open Representation

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]

/-- The native raw two-cocycle property for the action supplied by `ρ`. -/
def AllTwoCocyclesAreCoboundaries {M : Type uM} [AddCommGroup M] [Module R M]
    (ρ : Representation R G M) : Prop :=
  letI : SMul G M := ⟨fun g x => ρ g x⟩
  ∀ f : G × G → M,
    groupCohomology.IsCocycle₂ f → groupCohomology.IsCoboundary₂ f

private def d₁ {M : Type uM} [AddCommGroup M] [Module R M]
    (ρ : Representation R G M) (b : G → M) (p : G × G) : M :=
  ρ p.1 (b p.2) - b (p.1 * p.2) + b p.1

private theorem d₁_isCocycle₂ {M : Type uM} [AddCommGroup M] [Module R M]
    (ρ : Representation R G M) (b : G → M) :
    letI : SMul G M := ⟨fun g x => ρ g x⟩
    groupCohomology.IsCocycle₂ (d₁ ρ b) := by
  intro g h j
  change d₁ ρ b (g * h, j) + d₁ ρ b (g, h) =
    ρ g (d₁ ρ b (h, j)) + d₁ ρ b (g, h * j)
  simp only [d₁, map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
  abel

section Maps

variable {A : Type uA} {B : Type uB}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {ρA : Representation R G A} {ρB : Representation R G B}

private theorem map_d₁ (t : IntertwiningMap ρA ρB) (b : G → A) (p : G × G) :
    t (d₁ ρA b p) = d₁ ρB (fun g => t (b g)) p := by
  simp only [d₁, map_add, map_sub, t.isIntertwining]

private theorem map_isCocycle₂ (t : IntertwiningMap ρA ρB) (f : G × G → A) :
    (letI : SMul G A := ⟨fun g x => ρA g x⟩;
      groupCohomology.IsCocycle₂ f) →
    (letI : SMul G B := ⟨fun g x => ρB g x⟩;
      groupCohomology.IsCocycle₂ (fun p => t (f p))) := by
  intro hf g h j
  change t (f (g * h, j)) + t (f (g, h)) =
    ρB g (t (f (h, j))) + t (f (g, h * j))
  have he := congrArg t (hf g h j)
  change t (f (g * h, j) + f (g, h)) =
    t (ρA g (f (h, j)) + f (g, h * j)) at he
  simpa only [map_add, t.isIntertwining] using he

end Maps

/-- Pointwise lifting through an actual equivariant short exact sequence.
The carrier universes of `A`, `B`, and `C` are independent. -/
theorem allTwoCocyclesAreCoboundaries_of_shortExact
    {A : Type uA} {B : Type uB} {C : Type uC}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    {ρA : Representation R G A} {ρB : Representation R G B}
    {ρC : Representation R G C}
    (i : IntertwiningMap ρA ρB) (q : IntertwiningMap ρB ρC)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hexact : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hA : AllTwoCocyclesAreCoboundaries ρA)
    (hC : AllTwoCocyclesAreCoboundaries ρC) :
    AllTwoCocyclesAreCoboundaries ρB := by
  classical
  let : SMul G A := ⟨fun g x => ρA g x⟩
  let : SMul G B := ⟨fun g x => ρB g x⟩
  let : SMul G C := ⟨fun g x => ρC g x⟩
  intro f hf
  change ∀ g h j, f (g * h, j) + f (g, h) =
    ρB g (f (h, j)) + f (g, h * j) at hf
  obtain ⟨c, hc⟩ := hC (fun p => q (f p)) (map_isCocycle₂ q f hf)
  -- Only a set-theoretic, pointwise lift of the one-cochain is chosen.
  choose b hb using fun g : G => hq (c g)
  let r : G × G → B := fun p => f p - d₁ ρB b p
  have hrq (p : G × G) : q (r p) = 0 := by
    change q (f p - d₁ ρB b p) = 0
    rw [map_sub, map_d₁]
    have hbc : (fun g => q (b g)) = c := funext hb
    rw [hbc]
    change q (f p) - (ρC p.1 (c p.2) - c (p.1 * p.2) + c p.1) = 0
    have hc' : ρC p.1 (c p.2) - c (p.1 * p.2) + c p.1 = q (f p) := hc p.1 p.2
    rw [hc', sub_self]
  have hlift (p : G × G) : ∃ x : A, i x = r p := by
    have hm : r p ∈ LinearMap.ker q.toLinearMap :=
      LinearMap.mem_ker.mpr (hrq p)
    rw [← hexact] at hm
    exact hm
  choose a ha using hlift
  have hdb : groupCohomology.IsCocycle₂ (d₁ ρB b) := d₁_isCocycle₂ ρB b
  change ∀ g h j, d₁ ρB b (g * h, j) + d₁ ρB b (g, h) =
    ρB g (d₁ ρB b (h, j)) + d₁ ρB b (g, h * j) at hdb
  have hr : groupCohomology.IsCocycle₂ r := by
    intro g h j
    change (f (g * h, j) - d₁ ρB b (g * h, j)) +
        (f (g, h) - d₁ ρB b (g, h)) =
      ρB g (f (h, j) - d₁ ρB b (h, j)) +
        (f (g, h * j) - d₁ ρB b (g, h * j))
    rw [map_sub]
    calc
      _ = (f (g * h, j) + f (g, h)) -
          (d₁ ρB b (g * h, j) + d₁ ρB b (g, h)) := by abel
      _ = (ρB g (f (h, j)) + f (g, h * j)) -
          (ρB g (d₁ ρB b (h, j)) + d₁ ρB b (g, h * j)) := by
            rw [hf g h j, hdb g h j]
      _ = _ := by abel
  have hac : groupCohomology.IsCocycle₂ a := by
    intro g h j
    apply hi
    change i (a (g * h, j) + a (g, h)) =
      i (ρA g (a (h, j)) + a (g, h * j))
    have hr' : r (g * h, j) + r (g, h) =
        ρB g (r (h, j)) + r (g, h * j) := hr g h j
    simpa only [map_add, i.isIntertwining, ha] using hr'
  obtain ⟨a0, ha0⟩ := hA a hac
  refine ⟨fun g => b g + i (a0 g), ?_⟩
  intro g h
  change d₁ ρB (fun g => b g + i (a0 g)) (g, h) = f (g, h)
  calc
    _ = d₁ ρB b (g, h) + i (d₁ ρA a0 (g, h)) := by
      simp only [d₁, map_add, map_sub, i.isIntertwining]
      abel
    _ = d₁ ρB b (g, h) + i (a (g, h)) := by
      rw [show d₁ ρA a0 (g, h) = a (g, h) from ha0 g h]
    _ = d₁ ρB b (g, h) + r (g, h) := by rw [ha]
    _ = f (g, h) := by dsimp [r]; abel

section Filtration

variable {M : Type uM} [AddCommGroup M] [Module R M]
  {ρ : Representation R G M}

/-- `F k` pulled back along the native subtype of `F (k+1)`. -/
def filtrationStep (F : ℕ → Subrepresentation ρ) (k : ℕ) :
    Subrepresentation (F (k + 1)).toRepresentation where
  toSubmodule := (F k).toSubmodule.comap (F (k + 1)).toSubmodule.subtype
  apply_mem_toSubmodule g {x} hx := by
    change ρ g (x : M) ∈ (F k).toSubmodule
    exact (F k).apply_mem_toSubmodule g hx

/-- The actual successive quotient, with its inherited native action. -/
def filtrationGrade (F : ℕ → Subrepresentation ρ) (k : ℕ) :
    Representation R G
      ((F (k + 1)).toSubmodule ⧸ (filtrationStep F k).toSubmodule) :=
  (filtrationStep F k).quotient

/-- Graded primitives produce a primitive for each actual ambient cocycle.
This uses no splitting of the filtration and no global trace-one witness. -/
theorem isCoboundary₂_of_finite_stable_filtration
    (F : ℕ → Subrepresentation ρ) (hF : Monotone F) (n : ℕ)
    (hbot : F 0 = ⊥) (htop : F n = ⊤)
    (hgrade : ∀ k < n, AllTwoCocyclesAreCoboundaries (filtrationGrade F k))
    (f : G × G → M) :
    letI : SMul G M := ⟨fun g x => ρ g x⟩
    groupCohomology.IsCocycle₂ f → groupCohomology.IsCoboundary₂ f := by
  classical
  let : SMul G M := ⟨fun g x => ρ g x⟩
  intro hf
  have hpieces : ∀ k, k ≤ n → AllTwoCocyclesAreCoboundaries (F k).toRepresentation := by
    intro k
    induction k with
    | zero =>
      intro _ z _
      refine ⟨fun _ => 0, ?_⟩
      intro g h
      have hz : z (g, h) = 0 := by
        apply Subtype.ext
        have hm : (z (g, h) : M) ∈ (⊥ : Submodule R M) := by
          change (z (g, h) : M) ∈ (⊥ : Subrepresentation ρ)
          rw [← hbot]
          exact (z (g, h)).property
        exact (Submodule.mem_bot R).mp hm
      change (F 0).toRepresentation g 0 - 0 + 0 = z (g, h)
      rw [map_zero, sub_zero, add_zero, hz]
    | succ k ih =>
      intro hk
      have hkk : (F k).toSubmodule ≤ (F (k + 1)).toSubmodule := hF (Nat.le_succ k)
      let i : IntertwiningMap (F k).toRepresentation (F (k + 1)).toRepresentation :=
        { toLinearMap := Submodule.inclusion hkk
          isIntertwining' _ := by ext x; rfl }
      let q : IntertwiningMap (F (k + 1)).toRepresentation (filtrationGrade F k) :=
        { toLinearMap := (filtrationStep F k).toSubmodule.mkQ
          isIntertwining' _ := by ext x; rfl }
      have hi : Function.Injective i := Submodule.inclusion_injective hkk
      have hq : Function.Surjective q := (filtrationStep F k).toSubmodule.mkQ_surjective
      have hrange : LinearMap.range i.toLinearMap = (filtrationStep F k).toSubmodule := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          change (x : M) ∈ (F k).toSubmodule at hx
          refine ⟨⟨(x : M), hx⟩, ?_⟩
          exact Subtype.ext rfl
      have hexact : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap :=
        hrange.trans (Submodule.ker_mkQ (filtrationStep F k).toSubmodule).symm
      exact allTwoCocyclesAreCoboundaries_of_shortExact i q hi hq hexact
        (ih (Nat.le_of_succ_le hk)) (hgrade k (Nat.lt_of_succ_le hk))
  let ft : G × G → (F n).toSubmodule := fun p =>
    ⟨f p, by change f p ∈ F n; rw [htop]; trivial⟩
  let topInclusion : IntertwiningMap (F n).toRepresentation ρ :=
    { toLinearMap := (F n).toSubmodule.subtype
      isIntertwining' _ := by ext x; rfl }
  have hft :
      letI : SMul G (F n).toSubmodule := ⟨fun g x => (F n).toRepresentation g x⟩
      groupCohomology.IsCocycle₂ ft := by
    intro g h j
    apply Subtype.ext
    exact hf g h j
  obtain ⟨b, hb⟩ := hpieces n le_rfl ft hft
  refine ⟨fun g => topInclusion (b g), ?_⟩
  intro g h
  change d₁ ρ (fun g => topInclusion (b g)) (g, h) = f (g, h)
  rw [← map_d₁ topInclusion]
  exact congrArg topInclusion (hb g h)

end Filtration

end D5.S3.HomologicalAlgebra.FilteredTwoCocycle
