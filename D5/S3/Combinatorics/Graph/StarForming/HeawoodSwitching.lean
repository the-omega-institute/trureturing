/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodSwitching
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodSwitching
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The actual binary flag map and vertex-switching quotient. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Basic.ExistsUnique
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ReduceModChar

/-! The matrix model in HEAWOOD_DOUBLE_COVER_GAIN, at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The actual twenty-one incidence flags are used, not normalized
signatures or a finite list asserted to cover arbitrary graph covers. -/
namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodSwitching
open scoped BigOperators
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 128
abbrev F2 := ZMod 2
abbrev Mat := Matrix (Fin 3) (Fin 3) F2
abbrev Signing := Fin 21 → F2
abbrev Switches := Fin 14 → F2

def coordinate (p : Fin 7) (j : Fin 3) : F2 :=
  (((p.val+1) / 2^j.val % 2 : ℕ) : F2)

def flags : Fin 21 → Fin 7 × Fin 7 :=
  ![(0,1), (0,3), (0,5), (1,0), (1,3), (1,4), (2,2), (2,3), (2,6),
    (3,0), (3,1), (3,2), (4,1), (4,4), (4,6), (5,0), (5,5), (5,6),
    (6,2), (6,4), (6,5)]

/-- Every binary Fano flag occurs once in the twenty-one-coordinate signing. -/
theorem flags_complete : ∀ p l : Fin 7,
    (∑ j : Fin 3, coordinate p j * coordinate l j) = 0 ↔
      ∃! e : Fin 21, flags e = (p,l) := by
  change ∀ p l : Fin 7, _ ↔ ∃ e : Fin 21, flags e = (p,l) ∧
    ∀ e' : Fin 21, flags e' = (p,l) → e' = e
  decide +kernel

def phi : Signing →ₗ[F2] Mat where
  toFun s i j := ∑ e : Fin 21,
    s e * coordinate (flags e).1 i * coordinate (flags e).2 j
  map_add' s t := by
    ext i j
    change (∑ e : Fin 21, (s e+t e)*coordinate (flags e).1 i*coordinate (flags e).2 j) =
      (∑ e : Fin 21, s e*coordinate (flags e).1 i*coordinate (flags e).2 j) +
      (∑ e : Fin 21, t e*coordinate (flags e).1 i*coordinate (flags e).2 j)
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' a s := by
    ext i j
    change (∑ e : Fin 21, (a*s e)*coordinate (flags e).1 i*coordinate (flags e).2 j) =
      a * (∑ e : Fin 21, s e*coordinate (flags e).1 i*coordinate (flags e).2 j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

def switching : Switches →ₗ[F2] Signing where
  toFun s e := s ⟨(flags e).1.val,by have := (flags e).1.isLt; omega⟩ +
    s ⟨7+(flags e).2.val,by have := (flags e).2.isLt; omega⟩
  map_add' s t := by ext e; simp only [Pi.add_apply]; ring
  map_smul' a s := by ext e; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

/-- The flag outer products really are traceless. -/
theorem trace_phi (s : Signing) : Matrix.trace (phi s) = 0 := by
  have hi : ∀ e : Fin 21,
      (∑ i : Fin 3, coordinate (flags e).1 i * coordinate (flags e).2 i) = 0 := by
    decide +kernel
  change (∑ i : Fin 3, ∑ e : Fin 21,
    s e * coordinate (flags e).1 i * coordinate (flags e).2 i) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,hi,mul_zero]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- Vertex switching changes no matrix invariant; this is a symbolic identity
in all fourteen switch coordinates. -/
theorem phi_switching (s : Switches) : phi (switching s) = 0 := by
  ext i j
  change (∑ e : Fin 21, (switching s) e * coordinate (flags e).1 i * coordinate (flags e).2 j) = 0
  fin_cases i <;> fin_cases j <;>
    norm_num [switching,flags,coordinate,Fin.sum_univ_succ] <;> reduce_mod_char <;> try ring_nf
  all_goals
    reduce_mod_char
    first | rfl | simp [show (2 : F2) = 0 from by decide +kernel]

private def preimage (M : Mat) (e : Fin 21) : F2 :=
  match e.val with
  | 0 => M 0 1 + M 1 1
  | 1 => M 0 2 + M 2 2
  | 3 => M 1 0 + M 1 1
  | 4 => M 1 2
  | 6 => M 1 1
  | 9 => M 2 0 + M 2 2
  | 10 => M 2 1
  | 13 => M 2 2
  | _ => 0

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
/-- The six off-diagonal units and two explicit diagonal directions give an
actual preimage of every traceless matrix. -/
theorem phi_preimage (M : Mat) (hM : Matrix.trace M = 0) : phi (preimage M) = M := by
  have hchar : ∀ a b c : F2, a+b+c=0 → a=b+c := by decide +kernel
  have hd : M 0 0 = M 1 1 + M 2 2 := by
    apply hchar
    simpa [Matrix.trace,Fin.sum_univ_succ,add_assoc] using hM
  ext i j
  change (∑ e : Fin 21, preimage M e * coordinate (flags e).1 i * coordinate (flags e).2 j) = M i j
  fin_cases i <;> fin_cases j <;>
    norm_num [preimage,flags,coordinate,Fin.sum_univ_succ,hd] <;> reduce_mod_char <;> try ring_nf
  all_goals
    reduce_mod_char
    first | rfl | simp [show (2 : F2) = 0 from by decide +kernel]

def traceless : Submodule F2 Mat := LinearMap.ker (Matrix.traceLinearMap (Fin 3) F2 F2)

/-- Exact range, rather than only an eight-coordinate numerical rank claim. -/
theorem range_phi : LinearMap.range phi = traceless := by
  apply le_antisymm
  · rintro M ⟨s,rfl⟩
    exact trace_phi s
  · intro M hM
    exact ⟨preimage M,phi_preimage M hM⟩

private theorem switch_kernel_constant (s : Fin 14 → F2) (hs : switching s = 0) :
    ∀ v, s v = s 0 := by
  have hchar : ∀ a b : F2, a+b=0 → a=b := by decide +kernel
  have he (e : Fin 21) : s ⟨(flags e).1.val,by omega⟩ = s ⟨7+(flags e).2.val,by omega⟩ := by
    apply hchar
    exact congrFun hs e
  intro v
  fin_cases v
  · rfl
  · calc
      s 1 = s 10 := (he 4)
      _ = s 0 := (he 1).symm
  · calc
      s 2 = s 10 := (he 7)
      _ = s 0 := (he 1).symm
  · calc
      s 3 = s 8 := (he 10)
      _ = s 0 := (he 0).symm
  · calc
      s 4 = s 8 := (he 12)
      _ = s 0 := (he 0).symm
  · calc
      s 5 = s 12 := (he 16)
      _ = s 0 := (he 2).symm
  · calc
      s 6 = s 12 := (he 20)
      _ = s 0 := (he 2).symm
  · calc
      s 7 = s 3 := (he 9).symm
      _ = s 8 := (he 10)
      _ = s 0 := (he 0).symm
  · exact (he 0).symm
  · calc
      s 9 = s 3 := (he 11).symm
      _ = s 8 := (he 10)
      _ = s 0 := (he 0).symm
  · exact (he 1).symm
  · calc
      s 11 = s 4 := (he 13).symm
      _ = s 8 := (he 12)
      _ = s 0 := (he 0).symm
  · exact (he 2).symm
  · calc
      s 13 = s 4 := (he 14).symm
      _ = s 8 := (he 12)
      _ = s 0 := (he 0).symm

private def constants : F2 →ₗ[F2] LinearMap.ker switching where
  toFun a := ⟨fun _ => a,by
    change switching (fun _ => a) = 0
    ext e
    change a+a=0
    have h : ∀ a : F2, a+a=0 := by decide +kernel
    exact h a⟩
  map_add' a b := rfl
  map_smul' a b := rfl

private theorem constants_bijective : Function.Bijective constants := by
  constructor
  · intro a b he
    exact congrFun (congrArg Subtype.val he) 0
  · rintro ⟨s,hs⟩
    refine ⟨s 0,?_⟩
    apply Subtype.ext
    funext v
    exact (switch_kernel_constant s hs v).symm

private theorem switching_kernel_dimension : Module.finrank F2 (LinearMap.ker switching) = 1 := by
  have he := (LinearEquiv.ofBijective constants constants_bijective).finrank_eq
  simpa using he.symm

/-- The traceless matrix target has dimension eight. -/
theorem traceless_dimension : Module.finrank F2 traceless = 8 := by
  let t := Matrix.traceLinearMap (Fin 3) F2 F2
  have ht : Function.Surjective t := by
    intro a
    refine ⟨Matrix.diagonal (fun i : Fin 3 => if i=0 then a else 0),?_⟩
    simp [t]
  have hr : Module.finrank F2 (LinearMap.range t) = 1 := by
    rw [LinearMap.range_eq_top.mpr ht]
    simp
  have hm : Module.finrank F2 Mat = 9 := by simp [Mat,Module.finrank_matrix]
  have h := LinearMap.finrank_range_add_finrank_ker t
  change Module.finrank F2 (LinearMap.range t) + Module.finrank F2 traceless =
    Module.finrank F2 Mat at h
  omega

/-- The invariant's kernel is exactly vertex switching, by actual source
annihilation, surjectivity and the two rank-nullity calculations. -/
theorem kernel_phi_eq_switching : LinearMap.ker phi = LinearMap.range switching := by
  have hs : LinearMap.range switching ≤ LinearMap.ker phi := by
    rintro s ⟨v,rfl⟩
    exact phi_switching v
  have hp := LinearMap.finrank_range_add_finrank_ker phi
  have hd := LinearMap.finrank_range_add_finrank_ker switching
  have h21 : Module.finrank F2 Signing = 21 := by simp [Signing,Module.finrank_pi]
  have h14 : Module.finrank F2 Switches = 14 := by simp [Switches,Module.finrank_pi]
  have h8 : Module.finrank F2 (LinearMap.range phi) = 8 := by
    rw [range_phi]
    exact traceless_dimension
  have h1 := switching_kernel_dimension
  have he : Module.finrank F2 (LinearMap.range switching) =
      Module.finrank F2 (LinearMap.ker phi) := by omega
  exact (Submodule.eq_of_le_of_finrank_eq hs he).symm

/-- The actual signing quotient is linearly isomorphic to traceless matrices.
This is the full twenty-one-flag/switching correspondence, before graph
conjugacy, six-type classification or connectedness transfer. -/
noncomputable def switchingQuotientEquiv :
    (Signing ⧸ LinearMap.range switching) ≃ₗ[F2] traceless :=
  (Submodule.quotEquivOfEq _ _ kernel_phi_eq_switching.symm).trans
    (phi.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ range_phi))

end D5.S3.Combinatorics.Graph.StarForming.HeawoodSwitching
