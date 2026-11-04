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

end D5.S3.QuadraticForms.LieRadicalTransfer
