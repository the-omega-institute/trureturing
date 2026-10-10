/- GID: D5/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SurfaceObservers/NormalSubdirectInnerAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normal subdirect rigidity, perfectness and common inner actions. -/

import D5.S3.FiniteGroups.NikolovSegal.SmallTwistedGeneration
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Data.Fintype.Option
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
Finite subdirect products of nonabelian simple groups have no proper normal
subgroup surjecting onto every coordinate. The factors may be isomorphic;
no independence of their joint image is assumed. Finiteness of the factors
is unnecessary, while finiteness of the coordinate family is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.FiniteGroups.SurfaceObservers.NormalSubdirectInnerAction
open Subgroup
open scoped commutatorElement
universe u

variable {B A S : Type*} [Group B] [Group A] [Group S]

private theorem kernel_absorption
    (p : B →* A) (q : B →* S) (hfaith : Function.Injective (p.prod q))
    (M : Subgroup B) [M.Normal]
    (hM : M.map q = ⊤) (hK : p.ker.map q = ⊤)
    (hperfect : _root_.commutator S = ⊤) : p.ker ≤ M := by
  have himage : (⁅M, p.ker⁆).map q = ⊤ := by
    rw [Subgroup.map_commutator, hM, hK]
    exact hperfect
  intro k hk
  have hqk : q k ∈ (⁅M, p.ker⁆).map q := by rw [himage]; trivial
  obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hqk
  have hcp : p c = 1 := MonoidHom.mem_ker.mp (Subgroup.commutator_le_right M p.ker hc)
  have hkp : p k = 1 := MonoidHom.mem_ker.mp hk
  have hck : c = k := hfaith (Prod.ext (hcp.trans hkp.symm) hcq)
  exact hck ▸ Subgroup.commutator_le_left M p.ker hc

private theorem two_observer_rigidity [IsSimpleGroup S]
    (p : B →* A) (q : B →* S) (hfaith : Function.Injective (p.prod q))
    (hq : Function.Surjective q) (hnoncomm : ¬ IsMulCommutative S)
    (M : Subgroup B) [M.Normal]
    (hpM : M.map p = p.range) (hqM : M.map q = ⊤) : M = ⊤ := by
  have hknormal : (p.ker.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hkM : p.ker ≤ M := by
    rcases hknormal.eq_bot_or_eq_top with hzero | hfull
    · intro k hk
      have hqk : q k = 1 := by
        have : q k ∈ p.ker.map q := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
        simpa [hzero] using this
      have hkone : k = 1 := hfaith (Prod.ext
        ((MonoidHom.mem_ker.mp hk).trans (map_one p).symm)
        (hqk.trans (map_one q).symm))
      simp [hkone]
    · exact kernel_absorption p q hfaith M hqM hfull
        (NikolovSegal.SmallTwistedProduct.noncommutative_simple_commutator_top hnoncomm)
  exact Subgroup.map_injective_of_ker_le p hkM le_top
    (hpM.trans p.range_eq_map)


theorem finite_observer_rigidity (I : Type u) [Finite I]
    (S : I → Type u) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hnc : ∀ i, ¬ IsMulCommutative (S i))
    (G : Type u) [Group G] (f : ∀ i, G →* S i)
    (hfaith : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hsur : ∀ i, Function.Surjective (f i))
    (M : Subgroup G) [M.Normal] (hM : ∀ i, M.map (f i) = ⊤) : M = ⊤ := by
  let P : Type u → Prop := fun J =>
    ∀ (T : J → Type u) [∀ j, Group (T j)] [∀ j, IsSimpleGroup (T j)],
      (∀ j, ¬ IsMulCommutative (T j)) →
      ∀ (K : Type u) [Group K] (a : ∀ j, K →* T j),
        (∀ x y, (∀ j, a j x = a j y) → x = y) →
        (∀ j, Function.Surjective (a j)) →
        ∀ (N : Subgroup K) [N.Normal], (∀ j, N.map (a j) = ⊤) → N = ⊤
  have hP : P I := by
    apply Finite.induction_empty_option (P := P) _ _ _ I
    · intro J J' e ih T _ _ hnc K _ a hf hs N _ hN
      exact ih (fun j => T (e j)) (fun j => hnc (e j)) K (fun j => a (e j))
        (fun x y h => hf x y (fun j => by
          obtain ⟨i, rfl⟩ := e.surjective j
          exact h i)) (fun j => hs (e j)) N (fun j => hN (e j))
    · intro T _ _ hnc K _ a hf hs N _ hN
      apply top_unique
      intro x _
      have hx : x = 1 := hf x 1 (fun j => PEmpty.elim j)
      simp [hx]
    · intro J _ ih T _ _ hnc K _ a hf hs N _ hN
      let p : K →* (∀ j : J, T (some j)) := MonoidHom.pi (fun j => a (some j))
      let r : K →* p.range := p.rangeRestrict
      let b : ∀ j : J, p.range →* T (some j) :=
        fun j => (Pi.evalMonoidHom (fun j => T (some j)) j).comp p.range.subtype
      have hr : Function.Surjective r := p.rangeRestrict_surjective
      haveI : (N.map r).Normal := Subgroup.Normal.map inferInstance r hr
      have hcomp (j : J) : (b j).comp r = a (some j) := rfl
      have hNr : N.map r = ⊤ := ih (fun j => T (some j)) (fun j => hnc (some j))
        p.range b (by
          intro x y h
          apply Subtype.ext
          exact funext h) (by
          intro j s
          obtain ⟨k, hk⟩ := hs (some j) s
          exact ⟨r k, hk⟩) (N.map r) (by
          intro j
          rw [Subgroup.map_map, hcomp]
          exact hN (some j))
      refine two_observer_rigidity r (a none) ?_ (hs none) (hnc none) N ?_ ?_
      · intro x y h
        apply hf x y
        intro j
        cases j with
        | none => exact congrArg Prod.snd h
        | some j => exact congrArg (fun z : p.range × T none => (z.1 : ∀ j, T (some j)) j) h
      · exact hNr.trans (MonoidHom.range_eq_top.mpr hr).symm
      · exact hN none
  exact hP S hnc G f hfaith hsur M hM

theorem subdirect_perfect (I : Type u) [Finite I]
    (S : I → Type u) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
    (hnc : ∀ i, ¬ IsMulCommutative (S i))
    (G : Type u) [Group G] (f : ∀ i, G →* S i)
    (hfaith : ∀ x y, (∀ i, f i x = f i y) → x = y)
    (hsur : ∀ i, Function.Surjective (f i)) : _root_.commutator G = ⊤ := by
  apply finite_observer_rigidity I S hnc G f hfaith hsur (_root_.commutator G)
  intro i
  rw [_root_.map_commutator_eq, MonoidHom.range_eq_top.mpr (hsur i)]
  exact NikolovSegal.SmallTwistedProduct.noncommutative_simple_commutator_top (hnc i)


variable (I : Type u) [Finite I]
  (S : I → Type u) [∀ i, Group (S i)] [∀ i, IsSimpleGroup (S i)]
  (hnc : ∀ i, ¬ IsMulCommutative (S i))
  (E : Type u) [Group E] (rho : ∀ i, E →* S i)
  (N : Subgroup E) [N.Normal] (hN : ∀ i, N.map (rho i) = ⊤)

include hnc hN

theorem normal_joint_range : N.map (MonoidHom.pi rho) = (MonoidHom.pi rho).range := by
  let j : E →* (∀ i, S i) := MonoidHom.pi rho
  let r : E →* j.range := j.rangeRestrict
  let f : ∀ i, j.range →* S i :=
    fun i => (Pi.evalMonoidHom S i).comp j.range.subtype
  have hr : Function.Surjective r := j.rangeRestrict_surjective
  haveI : (N.map r).Normal := Subgroup.Normal.map inferInstance r hr
  have hf (i : I) : (f i).comp r = rho i := rfl
  have hNr : N.map r = ⊤ := finite_observer_rigidity I S hnc j.range f
    (by
      intro x y h
      apply Subtype.ext
      exact funext h)
    (by
      intro i s
      have hs : s ∈ N.map (rho i) := by rw [hN i]; trivial
      obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
      exact ⟨r x, hxs⟩)
    (N.map r) (by
      intro i
      rw [Subgroup.map_map, hf]
      exact hN i)
  calc
    N.map (MonoidHom.pi rho) = (N.map r).map j.range.subtype := by
      rw [Subgroup.map_map]
      rfl
    _ = j.range := by
      rw [hNr, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem common_lift (e : E) : ∃ n : N, ∀ i, rho i n = rho i e := by
  have he : (MonoidHom.pi rho) e ∈ N.map (MonoidHom.pi rho) := by
    rw [normal_joint_range I S hnc E rho N hN]
    exact ⟨e, rfl⟩
  obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp he
  exact ⟨⟨n, hn⟩, fun i => congrFun hne i⟩

/-- The same element of the normal subgroup realizes every coordinate action.
The automorphism of the actual joint image intertwines the quotient map with
ambient conjugation; its class modulo inner automorphisms is the identity.
Thus the induced outer action, including the action of the extension quotient,
is trivial. -/
theorem common_inner_action (e : E) :
    ∃ n : N,
      (∀ i, rho i n = rho i e) ∧
      (∀ (x : E) (i : I),
        rho i (e * x * e⁻¹) = rho i ((n : E) * x * (n : E)⁻¹)) ∧
      ∃ a : MulAut (N.map (MonoidHom.pi rho)),
        (∀ x : N,
          a ((MonoidHom.pi rho).subgroupMap N x) =
            (MonoidHom.pi rho).subgroupMap N (MulAut.conjNormal e x)) ∧
        a = MulAut.conj ((MonoidHom.pi rho).subgroupMap N n) ∧
        (QuotientGroup.mk a :
          MulAut (N.map (MonoidHom.pi rho)) ⧸
            (MulAut.conj : N.map (MonoidHom.pi rho) →*
              MulAut (N.map (MonoidHom.pi rho))).range) = QuotientGroup.mk 1 := by
  obtain ⟨n, hn⟩ := common_lift I S hnc E rho N hN e
  refine ⟨n, hn, ?_, MulAut.conj ((MonoidHom.pi rho).subgroupMap N n), ?_, rfl, ?_⟩
  · intro x i
    simp only [map_mul, map_inv, hn i]
  · intro x
    apply Subtype.ext
    funext i
    change rho i n * rho i x * (rho i n)⁻¹ = rho i (e * (x : E) * e⁻¹)
    simp only [map_mul, map_inv, hn i]
  · apply QuotientGroup.eq.mpr
    exact ⟨((MonoidHom.pi rho).subgroupMap N n)⁻¹, by simp⟩

end D5.S3.FiniteGroups.SurfaceObservers.NormalSubdirectInnerAction
