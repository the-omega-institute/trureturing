/- GID: D5/S3/HomologicalAlgebra/FilteredExtensionSplitting
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/FilteredExtensionSplitting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupExtension.Basic, mathlib/module/Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree]
   utility: none
   digest: Explicit trace contraction and native graded cocycle primitives construct homomorphic sections of arbitrary abelian-kernel extensions. -/

import D5.S3.HomologicalAlgebra.FilteredTwoCocycle
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

/-!
The explicit trace-one primitive uses native raw cocycles with precisely the
supplied representation. The contraction has orientation f = d₁ b; the native
coboundary adapter reverses it to d₁ b = f.

Factor extraction, the factor identity and section correction are shared by the
filtration and trace constructions. The filtration construction works for any
group. For a finite group, separate trace-one witnesses on the actual native
successive quotients give a homomorphic section of the original extension.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open groupCohomology
open D5.S3.HomologicalAlgebra.FilteredTwoCocycle

namespace D5.S3.HomologicalAlgebra.FilteredExtensionSplitting

universe uR uV uG uU uE

/-- An explicit finite trace-one primitive. -/
noncomputable def traceOnePrimitive
    {R : Type uR} {V : Type uV} {G : Type uG}
    [CommRing R] [AddCommGroup V] [Module R V]
    [Group G] [Fintype G]
    (rho : Representation R G V) (t : Module.End R V)
    (f : G × G → V) (g : G) : V :=
  ∑ x : G, rho x (t (f (x⁻¹, g)))

/-- The contraction identity, with orientation `f = d₁ b`.
The native raw cocycle predicate is evaluated using precisely `rho`. -/
theorem trace_one_primitive_spec
    {R : Type uR} {V : Type uV} {G : Type uG}
    [CommRing R] [AddCommGroup V] [Module R V]
    [Group G] [Fintype G]
    (rho : Representation R G V) (t : Module.End R V)
    (htrace : ∑ x : G, rho x * t * rho x⁻¹ = 1)
    (f : G × G → V)
    (hf : letI : SMul G V := ⟨fun g x => rho g x⟩; IsCocycle₂ f) :
    ∀ g h : G,
      f (g, h) =
        rho g (traceOnePrimitive rho t f h) -
          traceOnePrimitive rho t f (g * h) +
            traceOnePrimitive rho t f g := by
  classical
  have hco : ∀ g h k : G,
      f (g * h, k) + f (g, h) = rho g (f (h, k)) + f (g, h * k) := hf
  have htrace_apply (g h : G) :
      (∑ x : G, rho x (t (rho x⁻¹ (f (g, h))))) = f (g, h) := by
    have he := congrArg (fun q : Module.End R V => q (f (g, h))) htrace
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.one_apply] using he
  have hleft (g h : G) :
      (∑ x : G, rho x (t (f (x⁻¹ * g, h)))) =
        rho g (traceOnePrimitive rho t f h) := by
    calc
      (∑ x : G, rho x (t (f (x⁻¹ * g, h)))) =
          ∑ x : G, rho (g * x) (t (f (x⁻¹, h))) := by
        symm
        exact Fintype.sum_equiv (Equiv.mulLeft g)
          (fun x : G => rho (g * x) (t (f (x⁻¹, h))))
          (fun x : G => rho x (t (f (x⁻¹ * g, h))))
          (by intro x; simp [mul_assoc])
      _ = ∑ x : G, rho g (rho x (t (f (x⁻¹, h)))) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [map_mul, Module.End.mul_apply]
      _ = rho g (∑ x : G, rho x (t (f (x⁻¹, h)))) := by rw [map_sum]
      _ = rho g (traceOnePrimitive rho t f h) := by rfl
  intro g h
  have hsum :
      (∑ x : G, rho x (t (f (x⁻¹ * g, h)))) +
          (∑ x : G, rho x (t (f (x⁻¹, g)))) =
        (∑ x : G, rho x (t (rho x⁻¹ (f (g, h))))) +
          (∑ x : G, rho x (t (f (x⁻¹, g * h)))) := by
    calc
      (∑ x : G, rho x (t (f (x⁻¹ * g, h)))) +
          (∑ x : G, rho x (t (f (x⁻¹, g)))) =
          ∑ x : G, (rho x (t (f (x⁻¹ * g, h))) +
            rho x (t (f (x⁻¹, g)))) := Finset.sum_add_distrib.symm
      _ = ∑ x : G, (rho x (t (rho x⁻¹ (f (g, h)))) +
            rho x (t (f (x⁻¹, g * h)))) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' := congrArg (fun z : V => rho x (t z)) (hco x⁻¹ g h)
        simpa only [map_add] using hx'
      _ = (∑ x : G, rho x (t (rho x⁻¹ (f (g, h))))) +
          (∑ x : G, rho x (t (f (x⁻¹, g * h)))) := Finset.sum_add_distrib
  have hsum' := hsum
  rw [hleft g h, htrace_apply g h] at hsum'
  change rho g (traceOnePrimitive rho t f h) +
      traceOnePrimitive rho t f g =
    f (g, h) + traceOnePrimitive rho t f (g * h) at hsum'
  calc
    f (g, h) =
        (f (g, h) + traceOnePrimitive rho t f (g * h)) -
          traceOnePrimitive rho t f (g * h) := by abel
    _ = (rho g (traceOnePrimitive rho t f h) + traceOnePrimitive rho t f g) -
          traceOnePrimitive rho t f (g * h) := by rw [← hsum']
    _ = rho g (traceOnePrimitive rho t f h) -
          traceOnePrimitive rho t f (g * h) + traceOnePrimitive rho t f g := by abel

/-- The trace-one contraction supplies the native H²-triviality premise.
`IsCoboundary₂` requires `d₁ b = f`, hence the explicit symmetry below. -/
theorem all_two_cocycles_are_coboundaries_of_trace_one
    {R : Type uR} {V : Type uV} {G : Type uG}
    [CommRing R] [AddCommGroup V] [Module R V]
    [Group G] [Fintype G]
    (rho : Representation R G V) (t : Module.End R V)
    (htrace : ∑ g : G, rho g * t * rho g⁻¹ = 1) :
    AllTwoCocyclesAreCoboundaries rho := by
  letI : SMul G V := ⟨fun g x => rho g x⟩
  intro f hf
  refine ⟨traceOnePrimitive rho t f, ?_⟩
  intro g h
  exact (trace_one_primitive_spec rho t htrace f hf g h).symm

/-- The actual integral representation of the prescribed action on `Additive U`. -/
def phiRepresentation
    {U : Type uU} {G : Type uG} [CommGroup U] [Group G]
    (phi : G →* MulAut U) : Representation ℤ G (Additive U) :=
  letI : MulDistribMulAction G U := MulDistribMulAction.compHom U phi
  Representation.ofMulDistribMulAction G U

private theorem phi_representation_apply
    {U : Type uU} {G : Type uG} [CommGroup U] [Group G]
    (phi : G →* MulAut U) (g : G) (u : Additive U) :
    phiRepresentation phi g u = Additive.ofMul (phi g (Additive.toMul u)) := by
  rfl

/-- Native H²-triviality for the actual compatible action splits an extension.
There is no finite-group, trace-one, coefficient-section or splitting premise.
The kernel, extension and quotient group have independent universes.
The conclusion is propositional because native `S.Splitting` is a structure;
the consumers below choose an actual splitting from this proof. -/
theorem extension_splitting_of_all_two_cocycles_are_coboundaries
    {U : Type uU} {E : Type uE} {G : Type uG}
    [CommGroup U] [Group E] [Group G]
    (S : GroupExtension U E G) (phi : G →* MulAut U)
    (hcompat : ∀ (e : E) (u : U),
      S.inl (phi (S.rightHom e) u) = e * S.inl u * e⁻¹)
    (hH2 : AllTwoCocyclesAreCoboundaries (phiRepresentation phi)) :
    Nonempty S.Splitting := by
  classical
  letI : SMul G (Additive U) := ⟨fun g u => phiRepresentation phi g u⟩
  let sigma : S.Section := S.surjInvRightHom
  let c : G → G → U := fun g h =>
    Classical.choose
      (show sigma g * sigma h * (sigma (g * h))⁻¹ ∈ S.inl.range from
        GroupExtension.Section.mul_mul_mul_inv_mem_range_inl sigma g h)
  have hc_spec (g h : G) :
      S.inl (c g h) = sigma g * sigma h * (sigma (g * h))⁻¹ :=
    Classical.choose_spec
      (show sigma g * sigma h * (sigma (g * h))⁻¹ ∈ S.inl.range from
        GroupExtension.Section.mul_mul_mul_inv_mem_range_inl sigma g h)
  have hfactor (g h : G) :
      sigma g * sigma h = S.inl (c g h) * sigma (g * h) := by
    rw [hc_spec]
    group
  have hsigma_inl (g : G) (u : U) :
      sigma g * S.inl u = S.inl (phi g u) * sigma g := by
    calc
      sigma g * S.inl u =
          (sigma g * S.inl u * (sigma g)⁻¹) * sigma g := by group
      _ = S.inl (phi (S.rightHom (sigma g)) u) * sigma g := by rw [hcompat]
      _ = S.inl (phi g u) * sigma g := by
        rw [GroupExtension.Section.rightHom_section]
  have hcoc (g h k : G) :
      c g h * c (g * h) k = phi g (c h k) * c g (h * k) := by
    apply S.inl_injective
    have he :
        S.inl (c g h * c (g * h) k) * sigma (g * h * k) =
          S.inl (phi g (c h k) * c g (h * k)) * sigma (g * h * k) := by
      calc
        S.inl (c g h * c (g * h) k) * sigma (g * h * k) =
            S.inl (c g h) * (S.inl (c (g * h) k) * sigma (g * h * k)) := by
          rw [map_mul, mul_assoc]
        _ = S.inl (c g h) * (sigma (g * h) * sigma k) := by
          rw [← hfactor (g * h) k]
        _ = (S.inl (c g h) * sigma (g * h)) * sigma k := by rw [mul_assoc]
        _ = (sigma g * sigma h) * sigma k := by rw [← hfactor g h]
        _ = sigma g * (sigma h * sigma k) := by rw [mul_assoc]
        _ = sigma g * (S.inl (c h k) * sigma (h * k)) := by rw [hfactor h k]
        _ = (sigma g * S.inl (c h k)) * sigma (h * k) := by rw [mul_assoc]
        _ = (S.inl (phi g (c h k)) * sigma g) * sigma (h * k) := by
          rw [hsigma_inl]
        _ = S.inl (phi g (c h k)) * (sigma g * sigma (h * k)) := by rw [mul_assoc]
        _ = S.inl (phi g (c h k)) *
            (S.inl (c g (h * k)) * sigma (g * (h * k))) := by rw [hfactor g (h * k)]
        _ = S.inl (phi g (c h k) * c g (h * k)) * sigma (g * h * k) := by
          simp only [map_mul, mul_assoc]
    exact mul_right_cancel he
  let f : G × G → Additive U := fun p => Additive.ofMul (c p.1 p.2)
  have hf : IsCocycle₂ f := by
    intro g h k
    change f (g * h, k) + f (g, h) =
      phiRepresentation phi g (f (h, k)) + f (g, h * k)
    apply Additive.ext
    have he := (mul_comm (c (g * h) k) (c g h)).trans (hcoc g h k)
    simpa only [f, toMul_add, phi_representation_apply, toMul_ofMul] using he
  obtain ⟨b, hb⟩ := hH2 f hf
  let beta : G → U := fun g => Additive.toMul (b g)
  have hbmul (g h : G) :
      c g h = phi g (beta h) * (beta (g * h))⁻¹ * beta g := by
    have he := congrArg Additive.toMul (hb g h)
    change Additive.toMul
        (phiRepresentation phi g (b h) - b (g * h) + b g) =
      Additive.toMul (f (g, h)) at he
    simpa only [f, beta, toMul_add, toMul_sub, phi_representation_apply,
      toMul_ofMul, div_eq_mul_inv] using he.symm
  let delta : G → U := fun g => (beta g)⁻¹
  have hdelta_factor (g h : G) :
      delta g * phi g (delta h) * c g h = delta (g * h) := by
    simp only [delta, hbmul, map_inv]
    calc
      (beta g)⁻¹ * (phi g (beta h))⁻¹ *
          (phi g (beta h) * (beta (g * h))⁻¹ * beta g) =
          (beta g)⁻¹ * (beta (g * h))⁻¹ * beta g := by group
      _ = (beta (g * h))⁻¹ := by
        rw [mul_comm (beta g)⁻¹ (beta (g * h))⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  let s : G → E := fun g => S.inl (delta g) * sigma g
  have hs_mul (g h : G) : s (g * h) = s g * s h := by
    dsimp only [s]
    calc
      S.inl (delta (g * h)) * sigma (g * h) =
          S.inl (delta g * phi g (delta h) * c g h) * sigma (g * h) := by
        rw [hdelta_factor]
      _ = (S.inl (delta g) * sigma g) * (S.inl (delta h) * sigma h) := by
        symm
        calc
          (S.inl (delta g) * sigma g) * (S.inl (delta h) * sigma h) =
              S.inl (delta g) * (sigma g * S.inl (delta h)) * sigma h := by group
          _ = S.inl (delta g) *
              (S.inl (phi g (delta h)) * sigma g) * sigma h := by rw [hsigma_inl]
          _ = S.inl (delta g * phi g (delta h)) * (sigma g * sigma h) := by
            simp only [map_mul]
            group
          _ = S.inl (delta g * phi g (delta h) * c g h) * sigma (g * h) := by
            rw [hfactor g h]
            simp only [map_mul]
            group
  have hs_right : Function.RightInverse s S.rightHom := by
    intro g
    dsimp only [s]
    simp only [map_mul, GroupExtension.rightHom_inl,
      GroupExtension.Section.rightHom_section, one_mul]
  have hs_one : s 1 = 1 := by
    have h := hs_mul 1 1
    have he : (1 : E) * s 1 = s 1 * s 1 := by simpa using h
    exact (mul_right_cancel he).symm
  let sm : G →* E :=
    { toFun := s
      map_one' := hs_one
      map_mul' := hs_mul }
  exact ⟨{ __ := sm, rightInverse_rightHom := hs_right }⟩

/-- The actual extension consumer of the native finite-stable-filtration theorem.
Only the filtration length is finite; `G`, `U` and `E` may be infinite. -/
noncomputable def extension_splitting_of_finite_stable_filtration
    {U : Type uU} {E : Type uE} {G : Type uG}
    [CommGroup U] [Group E] [Group G]
    (S : GroupExtension U E G) (phi : G →* MulAut U)
    (hcompat : ∀ (e : E) (u : U),
      S.inl (phi (S.rightHom e) u) = e * S.inl u * e⁻¹)
    (F : ℕ → Subrepresentation (phiRepresentation phi))
    (hF : Monotone F) (n : ℕ) (hbot : F 0 = ⊥) (htop : F n = ⊤)
    (hgrade : ∀ k < n, AllTwoCocyclesAreCoboundaries (filtrationGrade F k)) :
    S.Splitting := by
  apply Classical.choice
  apply extension_splitting_of_all_two_cocycles_are_coboundaries S phi hcompat
  intro f hf
  exact is_coboundary_two_of_finite_stable_filtration F hF n hbot htop hgrade f hf

/-- The trace-one extension application, using the generic correction. -/
noncomputable def extension_splitting_of_trace_one
    {U : Type uU} {E : Type uE} {G : Type uG}
    [CommGroup U] [Group E] [Group G] [Fintype G]
    (S : GroupExtension U E G) (phi : G →* MulAut U)
    (hcompat : ∀ (e : E) (u : U),
      S.inl (phi (S.rightHom e) u) = e * S.inl u * e⁻¹)
    (t : Module.End ℤ (Additive U))
    (htrace : ∑ g : G,
      phiRepresentation phi g * t * phiRepresentation phi g⁻¹ = 1) :
    S.Splitting := by
  exact Classical.choice
    (extension_splitting_of_all_two_cocycles_are_coboundaries S phi hcompat
      (all_two_cocycles_are_coboundaries_of_trace_one (phiRepresentation phi) t htrace))

/-- Independent trace-one witnesses on the actual native grades split the extension.
No trace-one endomorphism on `Additive U` is assumed or produced. -/
noncomputable def extension_splitting_of_finite_stable_filtration_grade_trace_one
    {U : Type uU} {E : Type uE} {G : Type uG}
    [CommGroup U] [Group E] [Group G] [Fintype G]
    (S : GroupExtension U E G) (phi : G →* MulAut U)
    (hcompat : ∀ (e : E) (u : U),
      S.inl (phi (S.rightHom e) u) = e * S.inl u * e⁻¹)
    (F : ℕ → Subrepresentation (phiRepresentation phi))
    (hF : Monotone F) (n : ℕ) (hbot : F 0 = ⊥) (htop : F n = ⊤)
    (hgradeTrace : ∀ k < n,
      ∃ t : Module.End ℤ
          ((F (k + 1)).toSubmodule ⧸ (filtrationStep F k).toSubmodule),
        ∑ g : G, filtrationGrade F k g * t * filtrationGrade F k g⁻¹ = 1) :
    S.Splitting := by
  apply extension_splitting_of_finite_stable_filtration S phi hcompat F hF n hbot htop
  intro k hk
  obtain ⟨t, ht⟩ := hgradeTrace k hk
  exact all_two_cocycles_are_coboundaries_of_trace_one (filtrationGrade F k) t ht

end D5.S3.HomologicalAlgebra.FilteredExtensionSplitting
