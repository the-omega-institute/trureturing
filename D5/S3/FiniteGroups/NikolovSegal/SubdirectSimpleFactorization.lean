/- GID: D5/S3/FiniteGroups/NikolovSegal/SubdirectSimpleFactorization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/SubdirectSimpleFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A prescribed nonabelian simple quotient of a finite subdirect product factors through one coordinate. -/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Option

set_option autoImplicit false

namespace NikolovSegal

universe u v w z

/-- Two jointly separating homomorphisms have commuting kernels. A prescribed
surjection onto a nonabelian simple group therefore kills one of those kernels. -/
private theorem killed_kernel_of_separating_pair
    {G : Type u} {L : Type v} {R : Type z} {F : Type w}
    [Group G] [Group L] [Group R] [Group F] [IsSimpleGroup F]
    (noncomm : ¬ ∀ x y : F, x * y = y * x)
    (p : G →* L) (q : G →* R)
    (separate : ∀ x y : G, p x = p y → q x = q y → x = y)
    (theta : G →* F) (theta_onto : Function.Surjective theta) :
    p.ker ≤ theta.ker ∨ q.ker ≤ theta.ker := by
  haveI : (p.ker.map theta).Normal :=
    Subgroup.Normal.map inferInstance theta theta_onto
  haveI : (q.ker.map theta).Normal :=
    Subgroup.Normal.map inferInstance theta theta_onto
  rcases Subgroup.Normal.eq_bot_or_eq_top (p.ker.map theta) with hp | hp
  · left
    intro x hx
    have hmem : theta x ∈ p.ker.map theta := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hp, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.mpr hmem
  · rcases Subgroup.Normal.eq_bot_or_eq_top (q.ker.map theta) with hq | hq
    · right
      intro x hx
      have hmem : theta x ∈ q.ker.map theta := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hq, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    · exfalso
      apply noncomm
      intro a b
      have ha : a ∈ p.ker.map theta := hp ▸ Subgroup.mem_top a
      have hb : b ∈ q.ker.map theta := hq ▸ Subgroup.mem_top b
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
      have hx' : p x = 1 := MonoidHom.mem_ker.mp hx
      have hy' : q y = 1 := MonoidHom.mem_ker.mp hy
      have hxy : x * y = y * x := separate _ _
        (by simp only [map_mul, hx', one_mul, mul_one])
        (by simp only [map_mul, hy', one_mul, mul_one])
      simpa only [map_mul] using congrArg theta hxy

/-- Let an actual subgroup of a finite dependent product project onto every
factor. Every prescribed surjection from that subgroup onto a nonabelian simple
group factors through one of those coordinate projections. The factor groups
and the simple target may be infinite, and the index type may be empty. -/
theorem subdirect_simple_factorization
    {ι : Type u} [Finite ι] (A : ι → Type v) [∀ i, Group (A i)]
    {F : Type w} [Group F] [IsSimpleGroup F]
    (noncomm : ¬ ∀ x y : F, x * y = y * x)
    (B : Subgroup (∀ i, A i))
    (onto : ∀ i, Function.Surjective ((Pi.evalMonoidHom A i).comp B.subtype))
    (theta : B →* F) (theta_onto : Function.Surjective theta) :
    ∃ i : ι, ∃ phi : A i →* F, ∀ b : B, theta b = phi (b.val i) := by
  classical
  let P : Type u → Prop := fun I =>
    ∀ (G : Type (max u v)) [Group G]
      (K : I → Type v) [∀ i, Group (K i)] (p : ∀ i, G →* K i),
      (∀ i, Function.Surjective (p i)) →
      (∀ x y : G, (∀ i, p i x = p i y) → x = y) →
      ∀ (f : G →* F), Function.Surjective f →
        ∃ i : I, ∃ phi : K i →* F, ∀ x : G, f x = phi (p i x)
  have hfinite : P ι := by
    apply Finite.induction_empty_option (P := P) _ _ _ ι
    · intro I J e ih G _ K _ p hp hs f hf
      have hs' : ∀ x y : G, (∀ i, p (e i) x = p (e i) y) → x = y := by
        intro x y hxy
        apply hs x y
        intro j
        obtain ⟨i, rfl⟩ := e.surjective j
        exact hxy i
      obtain ⟨i, phi, hphi⟩ := ih G (fun i => K (e i))
        (fun i => p (e i)) (fun i => hp (e i)) hs' f hf
      exact ⟨e i, phi, hphi⟩
    · intro G _ K _ p hp hs f hf
      have hF : Subsingleton F := by
        constructor
        intro a b
        obtain ⟨x, rfl⟩ := hf a
        obtain ⟨y, rfl⟩ := hf b
        exact congrArg f (hs x y (fun i => nomatch i))
      exact False.elim (not_subsingleton F hF)
    · intro I _ ih G _ K _ p hp hs f hf
      let r : G →* (∀ i : I, K (some i)) :=
        { toFun := fun x i => p (some i) x
          map_one' := funext (fun i => (p (some i)).map_one)
          map_mul' := fun x y => funext (fun i => (p (some i)).map_mul x y) }
      have hsep : ∀ x y : G, p none x = p none y →
          r.rangeRestrict x = r.rangeRestrict y → x = y := by
        intro x y hnone hrest
        apply hs x y
        intro j
        cases j with
        | none => exact hnone
        | some i => exact congrArg (fun t : r.range => t.val i) hrest
      rcases killed_kernel_of_separating_pair noncomm (p none)
          r.rangeRestrict hsep f hf with hkill | hkill
      · let phi : K none →* F := (p none).liftOfSurjective (hp none) ⟨f, hkill⟩
        refine ⟨none, phi, ?_⟩
        intro x
        change f x = ((p none).liftOfRightInverse (Function.surjInv (hp none))
          (Function.rightInverse_surjInv (hp none)) ⟨f, hkill⟩) (p none x)
        rw [MonoidHom.liftOfRightInverse_comp_apply]
      · let fR : r.range →* F :=
          r.rangeRestrict.liftOfSurjective r.rangeRestrict_surjective ⟨f, hkill⟩
        have hdesc : ∀ x : G, fR (r.rangeRestrict x) = f x := by
          intro x
          change (r.rangeRestrict.liftOfRightInverse
            (Function.surjInv r.rangeRestrict_surjective)
            (Function.rightInverse_surjInv r.rangeRestrict_surjective)
            ⟨f, hkill⟩) (r.rangeRestrict x) = f x
          rw [MonoidHom.liftOfRightInverse_comp_apply]
        have hfR : Function.Surjective fR := by
          intro a
          obtain ⟨x, hx⟩ := hf a
          exact ⟨r.rangeRestrict x, (hdesc x).trans hx⟩
        let pR : ∀ i : I, r.range →* K (some i) := fun i =>
          (Pi.evalMonoidHom (fun j : I => K (some j)) i).comp r.range.subtype
        have hpR : ∀ i, Function.Surjective (pR i) := by
          intro i a
          obtain ⟨x, hx⟩ := hp (some i) a
          exact ⟨r.rangeRestrict x, hx⟩
        have hsR : ∀ x y : r.range, (∀ i, pR i x = pR i y) → x = y := by
          intro x y hxy
          apply Subtype.ext
          funext i
          exact hxy i
        obtain ⟨i, phi, hphi⟩ := ih r.range (fun i => K (some i)) pR hpR hsR fR hfR
        refine ⟨some i, phi, ?_⟩
        intro x
        exact (hdesc x).symm.trans (hphi (r.rangeRestrict x))
  exact hfinite B A (fun i => (Pi.evalMonoidHom A i).comp B.subtype) onto
    (fun x y hxy => Subtype.ext (funext hxy)) theta theta_onto

end NikolovSegal
