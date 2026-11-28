/- GID: D5/S1/Dynamics/OrbitClosure/WordBallTent
   generality: G
   mirror-B: D5/B/S1/Dynamics/OrbitClosure/WordBallTent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Continuous word-ball tents obstruct uniform invariance for infinite finitely generated actions. -/


module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Generators
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith
public import OmegaMath.Combinatorics.Graph.GroupWordMetric
public import OmegaBuild.Commands

@[expose] public section

/-! Word-ball constructions for continuous actions on compact metric spaces. -/

compile_only_with_mathlib

open Set Function
open scoped Pointwise

namespace D5.S1.Dynamics.OrbitClosure.WordBallTent

noncomputable section

local instance : DecidableEq G := Classical.decEq G

universe u v

variable {G : Type u} {X : Type v} [Group G] [MetricSpace X] [CompactSpace X]

private theorem finite_hom_of_finite_generators (S : Finset G)
    (hS : Subgroup.closure (S : Set G) = ⊤)
    {H : Type*} [Group H] [Finite H] : Finite (G →* H) := by
  classical
  let P : Group.Generators G S := Group.Generators.ofSet hS
  let e : (G →* H) → (S → H) := fun f s => f s
  apply Finite.of_injective e
  intro f g hfg
  apply P.hom_ext f g
  intro s
  exact congrFun hfg s

private def transportPerm {A B : Type*} (e : A ≃ B) :
    Equiv.Perm A →* Equiv.Perm B where
  toFun p := e.symm.trans (p.trans e)
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp

/-- Uniformly bounded finite orbits force finite image for a finitely generated group. -/
private theorem finite_image_of_bounded_orbits [MulAction G X]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
    (N : ℕ) (hfinite : ∀ x : X, Finite (MulAction.orbit G x))
    (hcard : ∀ x : X, Nat.card (MulAction.orbit G x) ≤ N) :
    Finite (MulAction.toPermHom G X).range := by
  classical
  letI (n : Fin (N + 1)) : Finite (G →* Equiv.Perm (Fin n.val)) :=
    finite_hom_of_finite_generators S hS
  let K : Subgroup G := ⨅ (n : Fin (N + 1)) (f : G →* Equiv.Perm (Fin n.val)), f.ker
  have hK : K.FiniteIndex := Subgroup.finiteIndex_iInf fun n =>
    Subgroup.finiteIndex_iInf fun f => inferInstance
  have hle : K ≤ (MulAction.toPermHom G X).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro x
    letI : Finite (MulAction.orbit G x) := hfinite x
    letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
    let n : Fin (N + 1) := ⟨Nat.card (MulAction.orbit G x), Nat.lt_succ_of_le (hcard x)⟩
    let e : MulAction.orbit G x ≃ Fin n.val :=
      Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
    let f : G →* Equiv.Perm (Fin n.val) :=
      (transportPerm e).comp (MulAction.toPermHom G (MulAction.orbit G x))
    have hfg : f g = 1 := MonoidHom.mem_ker.mp
      (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hg n) f)
    let q : MulAction.orbit G x := ⟨x, MulAction.mem_orbit_self x⟩
    have heq := congrArg (fun p : Equiv.Perm (Fin n.val) => p (e q)) hfg
    have hq : g • q = q := e.injective (by simpa [f, transportPerm] using heq)
    exact congrArg Subtype.val hq
  letI : (MulAction.toPermHom G X).ker.FiniteIndex := Subgroup.finiteIndex_of_le hle
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (MulAction.toPermHom G X)).toEquiv

/-- A single orbit escapes any prescribed finite collection of translates. -/
private theorem exists_orbit_outside_finset [MulAction G X]
    (S : Finset G) (hS : Subgroup.closure (S : Set G) = ⊤)
    (hinf : (Set.range (MulAction.toPermHom G X)).Infinite) (B : Finset G) :
    ∃ x : X, ∃ g : G, ∀ b ∈ B, b • x ≠ g • x := by
  classical
  by_contra! h
  have cover (x : X) : ∀ g : G, ∃ b ∈ B, b • x = g • x := h x
  let f (x : X) : B → MulAction.orbit G x :=
    fun b => ⟨b.1 • x, MulAction.mem_orbit x b.1⟩
  have hf (x : X) : Surjective (f x) := by
    rintro ⟨y, g, rfl⟩
    obtain ⟨b, hb, he⟩ := cover x g
    exact ⟨⟨b, hb⟩, Subtype.ext he⟩
  have hfinite (x : X) : Finite (MulAction.orbit G x) := Finite.of_surjective (f x) (hf x)
  have hcard (x : X) : Nat.card (MulAction.orbit G x) ≤ B.card := by
    simpa using Nat.card_le_card_of_surjective (f x) (hf x)
  letI : Finite (MulAction.toPermHom G X).range :=
    finite_image_of_bounded_orbits S hS B.card hfinite hcard
  apply hinf
  change Set.Finite ((MulAction.toPermHom G X).range : Set (Equiv.Perm X))
  exact Set.toFinite _

private def wordBall (S : Finset G) : ℕ → Finset G
  | 0 => {1}
  | n + 1 => wordBall S n ∪ S.biUnion (fun s => (wordBall S n).image (fun g => s * g))

private abbrev Fits (S : Finset G) (n : ℕ) (g : G) : Prop :=
  GroupWordMetric.Fits (S : Set G) n g

private theorem one_mem_wordBall (S : Finset G) (n : ℕ) : (1 : G) ∈ wordBall S n := by
  induction n with
  | zero => simp [wordBall]
  | succ n ih => exact Finset.mem_union_left _ ih

private theorem finite_wordBall (S : Finset G) (n : ℕ) : Set.Finite (wordBall S n : Set G) := by
  exact (wordBall S n).finite_toSet

private theorem fits_mem_wordBall {S : Finset G} {n : ℕ} {g : G} :
    Fits S n g → g ∈ wordBall S n := by
  rintro ⟨l, hlS, hlen, hprod⟩
  induction n generalizing l g with
  | zero =>
      have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst l
      simp_all [wordBall]
  | succ n ih =>
      by_cases hnil : l = []
      · subst l
        rw [← hprod]
        exact one_mem_wordBall S (n + 1)
      · obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hnil
        have htail : Fits S n t.prod := by
          refine ⟨t, ?_, ?_, rfl⟩
          · intro b hb
            exact hlS b (by simp [hb])
          · simpa using hlen
        have ht := ih t (fun b hb => hlS b (by simp [hb])) (by simpa using hlen) rfl
        have ha : a ∈ S := hlS a (by simp)
        rw [List.prod_cons] at hprod
        rw [← hprod]
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, ha,
            Finset.mem_image.mpr ⟨t.prod, ht, rfl⟩⟩)

private theorem mem_wordBall_fits {S : Finset G} {n : ℕ} {g : G} :
    g ∈ wordBall S n → Fits S n g := by
  induction n generalizing g with
  | zero =>
      intro hg
      have : g = 1 := by simpa [wordBall] using hg
      subst g
      exact ⟨[], by simp, by simp, rfl⟩
  | succ n ih =>
      intro hg
      rw [wordBall, Finset.mem_union] at hg
      rcases hg with hg | hg
      · rcases ih hg with ⟨l, hlS, hlen, hprod⟩
        exact ⟨l, hlS, hlen.trans (Nat.le_succ n), hprod⟩
      · rcases Finset.mem_biUnion.mp hg with ⟨a, ha, hg⟩
        rcases Finset.mem_image.mp hg with ⟨b, hb, rfl⟩
        rcases ih hb with ⟨l, hlS, hlen, hprod⟩
        refine ⟨a :: l, ?_, ?_, ?_⟩
        · intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ha
          · exact hlS c hc
        · simp only [List.length_cons]
          omega
        · simp only [List.prod_cons]
          rw [hprod]

private theorem generates_of_closure (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hS : Subgroup.closure (S : Set G) = ⊤) :
    GroupWordMetric.Generates (S : Set G) := by
  let H : Subgroup G := {
    carrier := {g | ∃ n, Fits S n g}
    one_mem' := ⟨0, GroupWordMetric.Fits.one⟩
    mul_mem' := by
      rintro a b ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, hm.mul hn⟩
    inv_mem' := by
      rintro a ⟨n, hn⟩
      exact ⟨n, hn.inv hsym⟩ }
  have hle : Subgroup.closure (S : Set G) ≤ H := (Subgroup.closure_le H).mpr
    (fun s hs => ⟨1, GroupWordMetric.Fits.of_mem hs⟩)
  intro g
  exact hle (hS ▸ Subgroup.mem_top g)

private theorem wordBall_length_iff (S : Finset G)
    (hgen : GroupWordMetric.Generates (S : Set G)) (n : ℕ) (g : G) :
    g ∈ wordBall S n ↔ GroupWordMetric.length hgen g ≤ n := by
  rw [GroupWordMetric.length_le_iff]
  exact ⟨mem_wordBall_fits, fits_mem_wordBall⟩

end
end D5.S1.Dynamics.OrbitClosure.WordBallTent
