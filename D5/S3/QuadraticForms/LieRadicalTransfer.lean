/- GID: D5/S3/QuadraticForms/LieRadicalTransfer
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/LieRadicalTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Solvable kernels identify the actual solvable radical quotient. -/

/-
admission_basis: escape-witness
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19944
utility none: structural radical and derived-series arguments.
escape_witness: solvable_of_solvable_kernel, derivedSeriesOfIdeal_map
The full arbitrary dependent Lie telescopes, exact source reconstruction,
lawful enrolled readout and variation/sensitivity remain unregistered.
  solvable_of_solvable_kernel: proof_shape: content;
    escape_witness: solvable_of_solvable_kernel;
    consumers: KMV full quotient kernel (in progress)
  derivedSeriesOfIdeal_map: proof_shape: content;
    escape_witness: derivedSeriesOfIdeal_map; consumers: solvable_map
  solvable_map: proof_shape: bind-only; escape_witness: none;
    consumers: kernel_eq_radical, hasTrivialRadical_of_separating_surjections
  kernel_eq_radical: proof_shape: bind-only; escape_witness: none;
    consumers: quotientEquiv_of_solvable_kernel
  hasTrivialRadical_of_separating_surjections: proof_shape: bind-only;
    escape_witness: none; consumers: OrthogonalLieStructure.so_four_hasTrivialRadical
-/

import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Nilpotent

/-!
Standard solvable-extension and radical arguments use mathlib's actual derived
series and radical. These are supporting mathematics for the Ma-then-Zhang
credited KMV evolution-algebra argument, not a claim of a new classical theorem.
This working module does not yet prove the complete evolution-algebra quotient.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.LieRadicalTransfer

open LieAlgebra LieIdeal

variable {k L M : Type*} [Field k] [LieRing L] [LieAlgebra k L]
variable [LieRing M] [LieAlgebra k M]

/-- A uniform two-step nilpotence bound, including the zero Lie algebra. -/
theorem nilpotent_of_triple_bracket_zero {L : Type*} [LieRing L] [LieAlgebra k L]
    (h : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = 0) : LieRing.IsNilpotent L := by
  apply LieModule.IsNilpotent.mk (R := k) (L := L) (M := L) (k := 2)
  simp only [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
  apply (LieSubmodule.lie_eq_bot_iff _ _).mpr
  intro x hx y hy
  have hy' : y ∈ (⁅(⊤ : LieIdeal k L), (⊤ : LieIdeal k L)⁆ : LieIdeal k L).toSubmodule := hy
  clear hy
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span] at hy'
  induction hy' using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      exact h x a.val b.val
  | zero => simp
  | add a b ha hb ia ib => simp [ia, ib]
  | smul c a ha ia => simp [ia]


theorem solvable_of_solvable_kernel (f : L →ₗ⁅k⁆ M)
    [IsSolvable f.ker] [IsSolvable M] : IsSolvable L := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable k M
  obtain ⟨m, hm⟩ := IsSolvable.solvable k f.ker
  have hle : derivedSeries k L n ≤ f.ker := by
    apply LieIdeal.map_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    exact (LieIdeal.derivedSeries_map_le (f := f) n).trans (by rw [hn])
  have hm' : derivedSeriesOfIdeal k L m f.ker = ⊥ :=
    (f.ker.derivedSeries_eq_bot_iff m).mp hm
  apply IsSolvable.mk (R := k) (k := m + n)
  change derivedSeriesOfIdeal k L (m + n) ⊤ = ⊥
  rw [derivedSeriesOfIdeal_add]
  exact le_antisymm ((derivedSeriesOfIdeal_mono hle m).trans (by rw [hm'])) bot_le

/-- Inverse images of solvable ideals under maps with solvable kernel are
solvable. No surjectivity is needed. -/
theorem solvable_comap (f : L →ₗ⁅k⁆ M) [IsSolvable f.ker]
    (I : LieIdeal k M) [IsSolvable I] : IsSolvable (I.comap f) := by
  let g : I.comap f →ₗ⁅k⁆ I :=
    { (f.comp (I.comap f).incl).toLinearMap.codRestrict I.toSubmodule (fun x => x.property) with
      map_lie' := fun {x y} => Subtype.ext (f.map_lie x.val y.val) }
  let h : g.ker →ₗ⁅k⁆ f.ker :=
    { ((I.comap f).incl.toLinearMap.comp g.ker.incl.toLinearMap).codRestrict f.ker.toSubmodule
        (fun x => by
          change f x.val.val = 0
          exact congrArg (fun z : I => z.val) (LieHom.mem_ker.mp x.property)) with
      map_lie' := fun {x y} => rfl }
  have hh : Function.Injective h := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) hxy
  haveI : IsSolvable g.ker := hh.lieAlgebra_isSolvable
  exact solvable_of_solvable_kernel g

private theorem derivedSeriesOfIdeal_map (f : L →ₗ⁅k⁆ M)
    (hf : Function.Surjective f) (I : LieIdeal k L) (n : ℕ) :
    (derivedSeriesOfIdeal k L n I).map f = derivedSeriesOfIdeal k M n (I.map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [derivedSeriesOfIdeal_succ, LieIdeal.map_bracket_eq f hf, ih]

private theorem solvable_map (f : L →ₗ⁅k⁆ M) (hf : Function.Surjective f)
    (I : LieIdeal k L) [IsSolvable I] : IsSolvable (I.map f) := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable k I
  have hn' := (I.derivedSeries_eq_bot_iff n).mp hn
  apply IsSolvable.mk (R := k) (k := n)
  apply ((I.map f).derivedSeries_eq_bot_iff n).mpr
  rw [← derivedSeriesOfIdeal_map f hf I n, hn']
  simp

theorem kernel_eq_radical [IsNoetherian k L]
    (f : L →ₗ⁅k⁆ M) (hf : Function.Surjective f)
    [IsSolvable f.ker] [HasTrivialRadical k M] : f.ker = radical k L := by
  apply le_antisymm ((LieIdeal.solvable_iff_le_radical k L f.ker).mp inferInstance)
  apply LieIdeal.map_eq_bot_iff.mp
  haveI : IsSolvable ((radical k L).map f) := solvable_map f hf (radical k L)
  exact HasTrivialRadical.eq_bot_of_isSolvable _

noncomputable def quotientEquiv_of_solvable_kernel [IsNoetherian k L]
    (f : L →ₗ⁅k⁆ M) (hf : Function.Surjective f)
    [IsSolvable f.ker] [HasTrivialRadical k M] : (L ⧸ radical k L) ≃ₗ⁅k⁆ M := by
  have hker := kernel_eq_radical f hf
  rw [← hker]
  refine f.quotKerEquivRange.trans (LieEquiv.ofBijective f.range.incl ⟨Subtype.val_injective, ?_⟩)
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨f x, ⟨x, rfl⟩⟩, rfl⟩

/-- A separating family of surjective maps to radical-free Lie algebras makes
the source radical-free. The family may be empty when the source is zero. -/
theorem hasTrivialRadical_of_separating_surjections {α : Type*}
    (H : α → Type*) [∀ a, LieRing (H a)] [∀ a, LieAlgebra k (H a)]
    [∀ a, HasTrivialRadical k (H a)]
    (f : ∀ a, L →ₗ⁅k⁆ H a) (hf : ∀ a, Function.Surjective (f a))
    (hsep : ∀ x : L, (∀ a, f a x = 0) → x = 0) : HasTrivialRadical k L := by
  apply (hasTrivialRadical_iff_no_abelian_ideals k L).mpr
  intro I hI
  haveI : IsLieAbelian I := hI
  have hm (a : α) : I.map (f a) = ⊥ := by
    haveI : IsSolvable (I.map (f a)) := solvable_map (f a) (hf a) I
    exact HasTrivialRadical.eq_bot_of_isSolvable _
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  apply hsep x
  intro a
  have hh := LieIdeal.mem_map (f := f a) hx
  simpa only [hm a, LieSubmodule.mem_bot] using hh

/-- A simple actual ideal survives every map with solvable kernel faithfully. -/
theorem injective_on_simple_ideal (f : L →ₗ⁅k⁆ M) [IsSolvable f.ker]
    (I : LieIdeal k L) [IsSimple k I] : Function.Injective (f.comp I.incl) := by
  let g := f.comp I.incl
  let h : g.ker →ₗ⁅k⁆ f.ker :=
    { (I.incl.toLinearMap.comp g.ker.incl.toLinearMap).codRestrict f.ker.toSubmodule
        (fun x => x.property) with map_lie' := fun {x y} => rfl }
  have hh : Function.Injective h := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) hxy
  haveI : IsSolvable g.ker := hh.lieAlgebra_isSolvable
  exact (LieHom.ker_eq_bot g).mp (HasTrivialRadical.eq_bot_of_isSolvable g.ker)

/-- A nonzero projection of a simple ideal onto a simple quotient factor is a
proved Lie equivalence. Both ideals and maps here are the actual objects. -/
noncomputable def simpleIdealEquiv_of_surjection [IsSimple k M]
    (f : L →ₗ⁅k⁆ M) (hf : Function.Surjective f)
    (I : LieIdeal k L) [IsSimple k I] (hx : ∃ x : I, f x.val ≠ 0) : I ≃ₗ⁅k⁆ M := by
  let g := f.comp I.incl
  have hk : g.ker = ⊥ := by
    rcases IsSimple.eq_bot_or_eq_top g.ker with h | h
    · exact h
    · obtain ⟨x,hx⟩ := hx
      have hxg : x ∈ g.ker := by rw [h]; exact LieSubmodule.mem_top x
      exact False.elim (hx (LieHom.mem_ker.mp hxg))
  have hJ : I.map f = ⊤ := by
    rcases IsSimple.eq_bot_or_eq_top (I.map f) with h | h
    · obtain ⟨x,hx⟩ := hx
      have hh := LieIdeal.mem_map (f := f) x.property
      rw [h, LieSubmodule.mem_bot] at hh
      exact False.elim (hx hh)
    · exact h
  refine LieEquiv.ofBijective g ⟨(LieHom.ker_eq_bot g).mp hk, ?_⟩
  intro y
  have hy : y ∈ I.map f := by rw [hJ]; exact LieSubmodule.mem_top y
  exact LieIdeal.mem_map_of_surjective hf hy

/-- Transport simplicity across a proved Lie equivalence. -/
theorem isSimple_of_equiv [IsSimple k L] (e : L ≃ₗ⁅k⁆ M) : IsSimple k M := by
  constructor
  · intro I
    rcases IsSimple.eq_bot_or_eq_top (I.comap e.toLieHom) with h | h
    · left
      apply le_antisymm ?_ bot_le
      intro x hx
      have hh : e.symm x ∈ I.comap e.toLieHom := by simpa using hx
      rw [h, LieSubmodule.mem_bot] at hh
      change x = 0
      simpa using congrArg e hh
    · right
      apply top_unique
      intro x hx
      have hh : e.symm x ∈ I.comap e.toLieHom := by rw [h]; exact LieSubmodule.mem_top _
      simpa using hh
  · intro h
    exact IsSimple.non_abelian k (e.injective.isLieAbelian h)

end D5.S3.QuadraticForms.LieRadicalTransfer
