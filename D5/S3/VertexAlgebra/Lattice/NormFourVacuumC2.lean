/- GID: D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NormFourVacuumC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual norm-four cyclic vacuum C2 quotient has dimension at most three. -/

import D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Basic
import Batteries.Tactic.OpenPrivate

/-! The literal C2 space uses two states from the same actual vacuum algebra.
Li, Abelianizing vertex algebras, math/0409140v1, Corollary 3.6 and
Proposition 3.7 provide classical context. The norm-four vector retains its
Dong-Mason-Zhu / Shimakura attribution. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2

open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeActualStateFieldCalculus LatticeActualStateDerivative
open NormFourVirasoroVector NormFourVacuumIrreducible
open scoped BigOperators VertexOperator

open private word word_mem all_modes_closed
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumIrreducible
open private full_field_closed translation_closed translation_axis vector_mem finite_sum_mem
  from D5.S3.VertexAlgebra.Lattice.NormFourVacuumVertexAlgebra

noncomputable section

/-- Literal actual C2 generators with both states in the vacuum span.
The ambient presentation avoids choosing representatives in a quotient;
the theorem below proves this span lies in the actual vacuum algebra. -/
def C2 (D : LatticeData) (a : Charge D) (s : ℂ) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {z | ∃ u v : Carrier D,
    u ∈ vacuumDescendants D a s ∧ v ∈ vacuumDescendants D a s ∧
      z = mu D u (-2) v}

private theorem generator_mem (D : LatticeData) (a : Charge D) (s : ℂ)
    (u v : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (hv : v ∈ vacuumDescendants D a s) : mu D u (-2) v ∈ C2 D a s :=
  Submodule.subset_span ⟨u, v, hu, hv, rfl⟩

private theorem c2_le (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    C2 D a s ≤ vacuumDescendants D a s := by
  apply Submodule.span_le.mpr
  rintro z ⟨u, v, hu, hv, rfl⟩
  exact full_field_closed D a ha s hs u hu (-2) v hv

private theorem vacuum_mem (D : LatticeData) (a : Charge D) (s : ℂ) :
    vacuum D ∈ vacuumDescendants D a s := word_mem D a s []

/-- Every actual derivative lies in C2, using the proved -2 creation law. -/
private theorem translation_mem_c2 (D : LatticeData) (a : Charge D) (s : ℂ)
    (u : Carrier D) (hu : u ∈ vacuumDescendants D a s) :
    translation D u ∈ C2 D a s := by
  rw [LatticeActualVertexAlgebra.translation_as_mode]
  exact generator_mem D a s u (vacuum D) hu (vacuum_mem D a s)

/-- All coefficients at most -2, derived by translating the LEFT state.
No arbitrary higher-mode/C2 closure is supplied as a hypothesis. -/
private theorem higher_product_mem (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (r : ℕ) (u v : Carrier D) (hu : u ∈ vacuumDescendants D a s)
    (hv : v ∈ vacuumDescendants D a s) :
    mu D u (-((r : ℤ) + 2)) v ∈ C2 D a s := by
  induction r generalizing u with
  | zero => simpa using generator_mem D a s u v hu hv
  | succ r ih =>
      have previous := ih (translation D u) (translation_closed D a ha s hs u hu)
      have derivative := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
        (state_derivative_modes D u (-((r : ℤ) + 2)))
      change mu D (translation D u) (-((r : ℤ) + 2)) v =
        -((-((r : ℤ) + 2) : ℤ) : ℂ) •
          mu D u (-((r : ℤ) + 2) - 1) v at derivative
      have scalar : -((-((r : ℤ) + 2) : ℤ) : ℂ) = (r + 2 : ℂ) := by
        push_cast
        ring
      rw [scalar] at derivative
      rw [derivative] at previous
      have nonzero : (r + 2 : ℂ) ≠ 0 := by
        exact_mod_cast (show r + 2 ≠ 0 by omega)
      have recovered := (C2 D a s).smul_mem (r + 2 : ℂ)⁻¹ previous
      simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul,
        Nat.cast_add, Nat.cast_one,
        show -((r : ℤ) + 2) - 1 = -(((r + 1 : ℕ) : ℤ) + 2) by omega]
        using recovered

/-- Actual L[-2] preserves C2. The complete integer commutator gives
only coefficients -3-j in its correction; every natural j is covered. -/
private theorem minus_two_c2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (z : Carrier D) (hz : z ∈ C2 D a s) :
    mode D a s (-2) z ∈ C2 D a s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨u, v, hu, hv, rfl⟩ := hz
      let terms (j : ℕ) : Carrier D := commutatorTerm D (vector D a s) u (-1) (-2) j v
      have finite : Function.HasFiniteSupport terms :=
        (commutator_terms_finite D (vector D a s) u (-1) (-2)).fun_comp
          (map_zero (LinearMap.applyₗ v))
      have each (j : ℕ) : terms j ∈ C2 D a s := by
        change StateFieldResidueReconstruction.integerBinomial (-1) j •
          mu D (mu D (vector D a s) j u) (-1 + -2 - j) v ∈ C2 D a s
        apply (C2 D a s).smul_mem
        have inner := full_field_closed D a ha s hs (vector D a s)
          (vector_mem D a ha s hs) j u hu
        have h := higher_product_mem D a ha s hs (j + 1)
          (mu D (vector D a s) j u) v inner hv
        simpa only [show -1 + -2 - (j : ℤ) = -(((j + 1 : ℕ) : ℤ) + 2) by omega]
          using h
      have correction := finite_sum_mem (C2 D a s) terms finite each
      have comm := congrArg (fun A : Module.End ℂ (Carrier D) => A v)
        (mode_commutator D (vector D a s) u (-1) (-2))
      have evaluation : (∑ᶠ j : ℕ, commutatorTerm D (vector D a s) u (-1) (-2) j) v =
          ∑ᶠ j : ℕ, terms j := by
        change (LinearMap.applyₗ v) (∑ᶠ j : ℕ, commutatorTerm D (vector D a s) u (-1) (-2) j) = _
        exact map_finsum (LinearMap.applyₗ v)
          (commutator_terms_finite D (vector D a s) u (-1) (-2))
      rw [evaluation] at comm
      change mode D a s (-2) (mu D u (-2) v) -
        mu D u (-2) (mode D a s (-2) v) = ∑ᶠ j : ℕ, terms j at comm
      have base := generator_mem D a s u (mode D a s (-2) v) hu
        (all_modes_closed D a ha s hs (-2) v hv)
      have total := (C2 D a s).add_mem correction base
      simpa only [← comm, sub_add_cancel] using total
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using (C2 D a s).add_mem hu hv
  | smul c u _ hu => simpa only [map_smul] using (C2 D a s).smul_mem c hu

/-- The actual six-level relation kills the cube modulo literal C2. -/
private theorem cube_mem_c2 (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    mode D a s (-2) (mode D a s (-2) (mode D a s (-2) (vacuum D))) ∈ C2 D a s := by
  have vac := vacuum_mem D a s
  have axis := vector_mem D a ha s hs
  have first := all_modes_closed D a ha s hs (-2) (vacuum D) vac
  have third := all_modes_closed D a ha s hs (-3) (vacuum D) vac
  have h33 : mode D a s (-3) (mode D a s (-3) (vacuum D)) ∈ C2 D a s := by
    simpa [mu, mode] using
      higher_product_mem D a ha s hs 0 (vector D a s)
        (mode D a s (-3) (vacuum D)) axis third
  have h42 : mode D a s (-4) (mode D a s (-2) (vacuum D)) ∈ C2 D a s := by
    simpa [mu, mode] using
      higher_product_mem D a ha s hs 1 (vector D a s)
        (mode D a s (-2) (vacuum D)) axis first
  have h6 : mode D a s (-6) (vacuum D) ∈ C2 D a s := by
    simpa [mu, mode] using
      higher_product_mem D a ha s hs 3 (vector D a s) (vacuum D) axis vac
  have null := NormFourVacuumNull.level_six_vacuum_null D a ha s hs
  have relation : (64 : ℂ) • mode D a s (-2)
      (mode D a s (-2) (mode D a s (-2) (vacuum D))) =
      -(93 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) +
        (264 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) +
        (108 : ℂ) • mode D a s (-6) (vacuum D) := by
    calc
      _ = ((64 : ℂ) • mode D a s (-2)
          (mode D a s (-2) (mode D a s (-2) (vacuum D))) +
          (93 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) -
          (264 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) -
          (108 : ℂ) • mode D a s (-6) (vacuum D)) -
          (93 : ℂ) • mode D a s (-3) (mode D a s (-3) (vacuum D)) +
          (264 : ℂ) • mode D a s (-4) (mode D a s (-2) (vacuum D)) +
          (108 : ℂ) • mode D a s (-6) (vacuum D) := by module
      _ = _ := by rw [null]; module
  have h64 := (C2 D a s).add_mem
    ((C2 D a s).add_mem ((C2 D a s).smul_mem (-93 : ℂ) h33)
      ((C2 D a s).smul_mem (264 : ℂ) h42))
    ((C2 D a s).smul_mem (108 : ℂ) h6)
  rw [← relation] at h64
  have recovered := (C2 D a s).smul_mem (64 : ℂ)⁻¹ h64
  norm_num [smul_smul] at recovered
  exact recovered

private def representatives (D : LatticeData) (a : Charge D) (s : ℂ)
    (i : Fin 3) : Carrier D := ((mode D a s (-2)) ^ i.val) (vacuum D)

private def small (D : LatticeData) (a : Charge D) (s : ℂ) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ (Set.range (representatives D a s))

private theorem representatives_mem (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) (i : Fin 3) :
    representatives D a s i ∈ vacuumDescendants D a s := by
  have iter (n : ℕ) : ((mode D a s (-2)) ^ n) (vacuum D) ∈ vacuumDescendants D a s := by
    induction n with
    | zero => simpa using vacuum_mem D a s
    | succ n ih =>
        simpa only [pow_succ', Module.End.mul_apply] using
          all_modes_closed D a ha s hs (-2) _ ih
  exact iter i.val

private theorem small_le (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    small D a s ≤ vacuumDescendants D a s := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  exact representatives_mem D a ha s hs i

/-- L[-2] preserves C2 plus the first three powers, with no PBW basis. -/
private theorem minus_two_small (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1)
    (u : Carrier D) (hu : u ∈ small D a s) :
    mode D a s (-2) u ∈ C2 D a s ⊔ small D a s := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      fin_cases i
      · apply Submodule.mem_sup_right
        exact Submodule.subset_span ⟨1, by simp [representatives]⟩
      · apply Submodule.mem_sup_right
        exact Submodule.subset_span ⟨2, by simp [representatives, pow_succ', Module.End.mul_apply]⟩
      · apply Submodule.mem_sup_left
        simpa [representatives, pow_succ', Module.End.mul_apply] using cube_mem_c2 D a ha s hs
  | zero => simp
  | add u v _ _ hu hv => simpa only [map_add] using
      (C2 D a s ⊔ small D a s).add_mem hu hv
  | smul c u _ hu => simpa only [map_smul] using
      (C2 D a s ⊔ small D a s).smul_mem c hu

/-- All finite negative words reduce modulo actual C2 to the three powers.
The L[-1] case uses actual translation on this cyclic span only. -/
private theorem three_spanning (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    vacuumDescendants D a s ≤ C2 D a s ⊔ small D a s := by
  apply Submodule.span_le.mpr
  rintro v ⟨w, rfl⟩
  induction w with
  | nil =>
      exact Submodule.mem_sup_right
        (Submodule.subset_span ⟨0, by simp [word, representatives]⟩)
  | cons k w ih =>
      change mode D a s (-((k : ℤ) + 1)) (word D a s w) ∈ _
      by_cases zero : k = 0
      · subst k
        have h := translation_mem_c2 D a s (word D a s w) (word_mem D a s w)
        rw [translation_axis D a ha s hs _ (word_mem D a s w)] at h
        simpa using (Submodule.mem_sup_left h :
          mode D a s (-1) (word D a s w) ∈ C2 D a s ⊔ small D a s)
      by_cases one : k = 1
      · subst k
        obtain ⟨u, hu, z, hz, he⟩ := Submodule.mem_sup.mp ih
        rw [← he, map_add]
        exact (C2 D a s ⊔ small D a s).add_mem
          (Submodule.mem_sup_left (minus_two_c2 D a ha s hs u hu))
          (minus_two_small D a ha s hs z hz)
      · have hk : 2 ≤ k := by omega
        have h := higher_product_mem D a ha s hs (k - 2) (vector D a s)
          (word D a s w) (vector_mem D a ha s hs) (word_mem D a s w)
        apply Submodule.mem_sup_left
        simpa only [mode, mu,
          show -((k : ℤ) + 1) + 1 = -(((k - 2 : ℕ) : ℤ) + 2) by omega]
          using h

/-- Actual C2-cofiniteness, with a concrete bound of three.
No independence claim for the three representatives is made. -/
theorem actual_vacuum_c2_cofinite (D : LatticeData) (a : Charge D)
    (ha : bilinear D a a = 4) (s : ℂ) (hs : s ^ 2 = 1) :
    let S := vacuumDescendants D a s
    let C := (C2 D a s).comap S.subtype
    C2 D a s ≤ S ∧
      FiniteDimensional ℂ (S ⧸ C) ∧ Module.finrank ℂ (S ⧸ C) ≤ 3 := by
  classical
  let S := vacuumDescendants D a s
  let C := (C2 D a s).comap S.subtype
  let Q := S ⧸ C
  let q : S →ₗ[ℂ] Q := C.mkQ
  have cle := c2_le D a ha s hs
  have sle := small_le D a ha s hs
  let r : Fin 3 → S := fun i => ⟨representatives D a s i, representatives_mem D a ha s hs i⟩
  let R : Submodule ℂ Q := Submodule.span ℂ (Set.range fun i => q (r i))
  have small_image_aux : small D a s ≤ (R.comap q).map S.subtype := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨r i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  have small_image (z : Carrier D) (hz : z ∈ small D a s) : q ⟨z, sle hz⟩ ∈ R := by
    obtain ⟨w, hw, he⟩ := Submodule.mem_map.mp (small_image_aux hz)
    have equal : w = ⟨z, sle hz⟩ := Subtype.ext he
    exact equal ▸ hw
  have span_top : R = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨v, rfl⟩ := C.mkQ_surjective x
    obtain ⟨u, hu, z, hz, eq⟩ := Submodule.mem_sup.mp
      (three_spanning D a ha s hs v.property)
    have hzero : q ⟨u, cle hu⟩ = 0 := (Submodule.Quotient.mk_eq_zero C).mpr hu
    have split : (⟨u, cle hu⟩ : S) + ⟨z, sle hz⟩ = v := Subtype.ext eq
    rw [← split, map_add, hzero, zero_add]
    exact small_image z hz
  have finite : FiniteDimensional ℂ Q := Module.Finite.of_fg_top (by
    rw [← span_top]
    exact Submodule.fg_span (Set.finite_range _))
  have bound : Module.finrank ℂ Q ≤ 3 := by
    simpa using (finrank_le_of_span_eq_top span_top)
  exact ⟨cle, finite, bound⟩

end
end D5.S3.VertexAlgebra.Lattice.NormFourVacuumC2
