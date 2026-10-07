/- GID: D5/S3/Quantum/Information/BinaryLagrangianGraphForm
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/BinaryLagrangianGraphForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local coordinate swaps and a diagonal shear put binary Lagrangians in graph form. -/

/-
proof_shape:
  sp, swapAt: bind-only definitions earned by lagrangian_graph_form.
  swapLinear, xproj, eraseAt: bind-only private linear-map constructions; consumers are
    rank_swap_increase, exists_injective_mask and graph_of_injective.
  swapAt_involutive, sp_swapAt, swapAt_toggle, eraseAt_injective_on: bind-only, consumed helpers.
  rank_swap_increase: content; isotropy makes coordinate erasure injective on the old image,
    whose erased image is properly contained in the toggled projection image.
  exists_injective_mask: content, consuming rank_swap_increase at a maximizing mask.
  graph_of_injective: bind-only, consumed by lagrangian_graph_form; the inverse projection and
    isotropy on coordinate preimages give the symmetric matrix.
  lagrangian_graph_form: content, consuming exists_injective_mask and graph_of_injective.
escape_witness: rank_swap_increase is on the live path through exists_injective_mask to
  lagrangian_graph_form; its strict rank increase constructs a mask with invertible projection.
admission_basis: escape-witness (research line #13575, route step 1a)
Direct frozen dependencies: none (pinned Mathlib only).
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.BinaryLagrangianGraphForm

open scoped BigOperators symmDiff
open Matrix

local notation "V" N:arg => (Fin N → ZMod 2)
local notation "E" N:arg => ((V N) × (V N))

/-- The binary symplectic form in position and momentum coordinates. -/
def sp {N : ℕ} (u v : E N) : ZMod 2 :=
  ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)

/-- Swap position and momentum exactly at the coordinates in `H`. -/
def swapAt {N : ℕ} (H : Finset (Fin N)) (v : E N) : E N :=
  (fun i => if i ∈ H then v.2 i else v.1 i,
   fun i => if i ∈ H then v.1 i else v.2 i)

private def swapLinear {N : ℕ} (H : Finset (Fin N)) : E N →ₗ[ZMod 2] E N where
  toFun := swapAt H
  map_add' := by
    intro u v
    ext i <;> by_cases hi : i ∈ H <;> simp [swapAt, hi]
  map_smul' := by
    intro a v
    ext i <;> by_cases hi : i ∈ H <;> simp [swapAt, hi]

lemma swapAt_involutive {N : ℕ} (H : Finset (Fin N)) (v : E N) :
    swapAt H (swapAt H v) = v := by
  ext i <;> by_cases hi : i ∈ H <;> simp [swapAt, hi]

private lemma sp_swapAt {N : ℕ} (H : Finset (Fin N)) (u v : E N) :
    sp (swapAt H u) (swapAt H v) = sp u v := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ H <;> simp [swapAt, hi, add_comm]

private lemma swapAt_toggle {N : ℕ} (H : Finset (Fin N)) (i : Fin N) (v : E N) :
    swapAt (H ∆ {i}) v = swapAt {i} (swapAt H v) := by
  ext j <;> by_cases hj : j = i <;> by_cases hH : j ∈ H <;>
    simp [swapAt, Finset.mem_symmDiff, hj, hH]

private def xproj {N : ℕ} (H : Finset (Fin N)) (L : Submodule (ZMod 2) (E N)) :
    L →ₗ[ZMod 2] V N :=
  (LinearMap.fst (ZMod 2) (V N) (V N)).comp ((swapLinear H).comp L.subtype)

private def eraseAt {N : ℕ} (i : Fin N) : V N →ₗ[ZMod 2] V N where
  toFun := fun x j => if j = i then 0 else x j
  map_add' := by intro x y; ext j; by_cases h : j = i <;> simp [h]
  map_smul' := by intro a x; ext j; by_cases h : j = i <;> simp [h]

private lemma eraseAt_injective_on {N : ℕ} (S : Submodule (ZMod 2) (V N)) (i : Fin N)
    (hi : Pi.single i (1 : ZMod 2) ∉ S) :
    Function.Injective ((eraseAt i).domRestrict S) := by
  intro x y hxy
  have hout : ∀ j, j ≠ i → (x : V N) j = (y : V N) j := by
    intro j hj
    have h := congrFun hxy j
    simpa [eraseAt, hj] using h
  have hdiff : (x : V N) - (y : V N) =
      ((x : V N) i - (y : V N) i) • Pi.single i (1 : ZMod 2) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, hout j hj]
  have heq : (x : V N) i = (y : V N) i := by
    by_contra hne
    have hc : (x : V N) i - (y : V N) i ≠ 0 := sub_ne_zero.mpr hne
    apply hi
    have he : Pi.single i (1 : ZMod 2) =
        ((x : V N) i - (y : V N) i)⁻¹ • ((x : V N) - (y : V N)) := by
      rw [hdiff, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [he]
    exact S.smul_mem _ (S.sub_mem x.property y.property)
  apply Subtype.ext
  ext j
  by_cases hj : j = i
  · subst j; exact heq
  · exact hout j hj

private lemma rank_swap_increase {N : ℕ} (L : Submodule (ZMod 2) (E N))
    (hiso : ∀ u ∈ L, ∀ v ∈ L, sp u v = 0)
    (H : Finset (Fin N)) (u : L) (hu : xproj H L u = 0) (i : Fin N)
    (hui : (swapAt H u).2 i = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (xproj H L)) <
      Module.finrank (ZMod 2) (LinearMap.range (xproj (H ∆ {i}) L)) := by
  classical
  let p := xproj H L
  let q := xproj (H ∆ {i}) L
  let R := LinearMap.range p
  let T := LinearMap.range q
  let e : V N := Pi.single i 1
  have hx : (swapAt H u).1 = 0 := hu
  have heR : e ∉ R := by
    rintro ⟨v, hv⟩
    have hvx : (swapAt H v).1 = e := hv
    have h := hiso u u.property v v.property
    rw [← sp_swapAt H] at h
    simp [sp, hx, hvx, e, Pi.single_apply, mul_ite, hui] at h
  let Q := R.map (eraseAt i)
  have hQT : Q ≤ T := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨v, hv⟩ := hy
    let c := (swapAt H v).2 i
    refine ⟨v - c • u, ?_⟩
    change (swapAt (H ∆ {i}) ((v - c • u : L) : E N)).1 = eraseAt i y
    rw [swapAt_toggle]
    have hs : swapAt H ((v - c • u : L) : E N) =
        swapAt H v - c • swapAt H u := by
      change swapLinear H ((v : E N) - c • (u : E N)) = _
      rw [map_sub, map_smul]
      rfl
    rw [hs]
    have hvx : (swapAt H v).1 = y := hv
    ext j
    change (if j ∈ ({i} : Finset (Fin N)) then
      (swapAt H v).2 j - c * (swapAt H u).2 j
      else (swapAt H v).1 j - c * (swapAt H u).1 j) =
        if j = i then 0 else y j
    simp only [Finset.mem_singleton]
    by_cases hj : j = i
    · subst j
      simp only [ite_true, hui, mul_one]
      exact sub_self c
    · simp only [if_neg hj, hx, Pi.zero_apply, mul_zero, sub_zero]
      exact congrFun hvx j
  have heT : e ∈ T := by
    refine ⟨u, ?_⟩
    change (swapAt (H ∆ {i}) (u : E N)).1 = e
    rw [swapAt_toggle]
    ext j
    change (if j ∈ ({i} : Finset (Fin N)) then (swapAt H u).2 j
      else (swapAt H u).1 j) = e j
    simp only [Finset.mem_singleton]
    by_cases hj : j = i
    · subst j; simpa only [e, ite_true, Pi.single_eq_same] using hui
    · simp [e, hj, hx]
  have heQ : e ∉ Q := by
    rintro ⟨y, _, hy⟩
    have h := congrFun hy i
    simp [eraseAt, e] at h
  have hstrict : Q < T := lt_of_le_of_ne hQT (by
    intro h
    exact heQ (h.symm ▸ heT))
  have hrank : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) R := by
    change Module.finrank (ZMod 2) (R.map (eraseAt i)) = _
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (eraseAt_injective_on R i heR)
  have hlt := Submodule.finrank_lt_finrank_of_lt hstrict
  rw [hrank] at hlt
  exact hlt

private lemma exists_injective_mask {N : ℕ} (L : Submodule (ZMod 2) (E N))
    (hiso : ∀ u ∈ L, ∀ v ∈ L, sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = N) :
    ∃ H : Finset (Fin N), Function.Injective (xproj H L) := by
  classical
  obtain ⟨H, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset (Fin N)))
    (fun H => Module.finrank (ZMod 2) (LinearMap.range (xproj H L)))
    Finset.univ_nonempty
  let p := xproj H L
  have hrle : Module.finrank (ZMod 2) (LinearMap.range p) ≤ N := by
    simpa using (LinearMap.range p).finrank_le
  have hr : Module.finrank (ZMod 2) (LinearMap.range p) = N := by
    by_contra hne
    have hlt : Module.finrank (ZMod 2) (LinearMap.range p) < N :=
      lt_of_le_of_ne hrle hne
    have hRN := p.finrank_range_add_finrank_ker
    rw [hdim] at hRN
    have hkdim : 0 < Module.finrank (ZMod 2) (LinearMap.ker p) := by omega
    have hk : LinearMap.ker p ≠ ⊥ := Submodule.one_le_finrank_iff.mp hkdim
    obtain ⟨u, hu, hune⟩ := (LinearMap.ker p).ne_bot_iff.mp hk
    change xproj H L u = 0 at hu
    have hx : (swapAt H u).1 = 0 := hu
    have hz : (swapAt H u).2 ≠ 0 := by
      intro hz
      have hsw : swapAt H (u : E N) = 0 := Prod.ext hx hz
      have h := congrArg (swapAt H) hsw
      rw [swapAt_involutive] at h
      have hzero : swapAt H (0 : E N) = 0 := (swapLinear H).map_zero
      exact hune (Subtype.ext (h.trans hzero))
    obtain ⟨i, hi⟩ : ∃ i, (swapAt H u).2 i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    let c := (swapAt H u).2 i
    let w : L := c⁻¹ • u
    have hw : xproj H L w = 0 := by
      simp only [w, map_smul, hu, smul_zero]
    have hwi : (swapAt H w).2 i = 1 := by
      change ((swapLinear H) (c⁻¹ • (u : E N))).2 i = 1
      rw [map_smul]
      exact inv_mul_cancel₀ hi
    have hinc := rank_swap_increase L hiso H w hw i hwi
    exact (Nat.not_lt_of_ge (hmax (H ∆ {i}) (Finset.mem_univ _))) hinc
  refine ⟨H, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.finrank_eq_zero.mp
  change Module.finrank (ZMod 2) (LinearMap.ker p) = 0
  have hRN := p.finrank_range_add_finrank_ker
  rw [hr, hdim] at hRN
  omega

private lemma graph_of_injective {N : ℕ} (L : Submodule (ZMod 2) (E N))
    (hiso : ∀ u ∈ L, ∀ v ∈ L, sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = N)
    (H : Finset (Fin N)) (hinj : Function.Injective (xproj H L)) :
    ∃ A : Matrix (Fin N) (Fin N) (ZMod 2), A.IsSymm ∧
      ∀ v : E N, v ∈ L ↔ (swapAt H v).2 = A *ᵥ (swapAt H v).1 := by
  classical
  have hd : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) (V N) := by
    simpa using hdim
  let e := (xproj H L).linearEquivOfInjective hinj hd
  let g : V N →ₗ[ZMod 2] E N :=
    (swapLinear H).comp (L.subtype.comp e.symm.toLinearMap)
  let f : V N →ₗ[ZMod 2] V N := (LinearMap.snd (ZMod 2) (V N) (V N)).comp g
  let A := LinearMap.toMatrix' f
  have hx : ∀ x, (g x).1 = x := by
    intro x
    exact e.apply_symm_apply x
  have hg : ∀ x y, sp (g x) (g y) = 0 := by
    intro x y
    change sp (swapAt H (e.symm x : E N)) (swapAt H (e.symm y : E N)) = 0
    rw [sp_swapAt]
    exact hiso _ (e.symm x).property _ (e.symm y).property
  refine ⟨A, ?_, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    change f (Pi.single i 1) j = f (Pi.single j 1) i
    have h := hg (Pi.single i 1) (Pi.single j 1)
    have hpair : f (Pi.single i 1) j + f (Pi.single j 1) i = 0 := by
      simpa [sp, hx, f, Pi.single_apply, Finset.sum_add_distrib, mul_ite, ite_mul,
        add_comm] using h
    exact (eq_neg_of_add_eq_zero_left hpair).trans (CharTwo.neg_eq _)
  · intro v
    rw [LinearMap.toMatrix'_mulVec]
    constructor
    · intro hv
      have hrec : e.symm (swapAt H v).1 = ⟨v, hv⟩ := by
        exact e.symm_apply_apply ⟨v, hv⟩
      change (swapAt H v).2 = (swapAt H (e.symm (swapAt H v).1 : E N)).2
      rw [hrec]
    · intro hv
      have he : swapAt H v = g (swapAt H v).1 := Prod.ext (hx _).symm hv
      have h := congrArg (swapAt H) he
      have hv' : v = (e.symm (swapAt H v).1 : E N) := by
        simpa [g, LinearMap.comp_apply, swapLinear, swapAt_involutive] using h
      rw [hv']
      exact (e.symm (swapAt H v).1).property

/-- Every binary Lagrangian becomes a graph with symmetric zero-diagonal adjacency after
local Hadamard swaps and the diagonal phase shear specified by `d`. -/
theorem lagrangian_graph_form {N : ℕ}
    (L : Submodule (ZMod 2) (E N))
    (hiso : ∀ u ∈ L, ∀ v ∈ L, sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = N) :
    ∃ (H : Finset (Fin N)) (d : V N)
      (Γ : Matrix (Fin N) (Fin N) (ZMod 2)),
      Γ.IsSymm ∧ (∀ i, Γ i i = 0) ∧
      ∀ v : E N, v ∈ L ↔
        (swapAt H v).2 + (fun i => d i * (swapAt H v).1 i) =
          Γ *ᵥ (swapAt H v).1 := by
  obtain ⟨H, hinj⟩ := exists_injective_mask L hiso hdim
  obtain ⟨A, hA, hgraph⟩ := graph_of_injective L hiso hdim H hinj
  let d : V N := fun i => A i i
  refine ⟨H, d, A + Matrix.diagonal d, hA.add (Matrix.isSymm_diagonal d), ?_, ?_⟩
  · intro i
    simp [d, CharTwo.add_self_eq_zero]
  · intro v
    rw [hgraph, Matrix.add_mulVec]
    have hd : Matrix.diagonal d *ᵥ (swapAt H v).1 =
        fun i => d i * (swapAt H v).1 i :=
      funext (Matrix.mulVec_diagonal d (swapAt H v).1)
    rw [hd]
    exact add_right_cancel_iff.symm

end D5.S3.Quantum.Information.BinaryLagrangianGraphForm
