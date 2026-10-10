/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPositiveSylow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitarySylowNormalizer
import Mathlib.Algebra.CharP.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace NikolovSegal.UnitarySylow
open Matrix SLnNormalizer PartIIUnitaryUpperTorus
universe u
variable {F : Type u} [Field F] {n : ℕ}

theorem upper_pow {A : SpecialLinearGroup (Fin n) F} (hA : Upper A) (m : ℕ) :
    Upper (A^m) := by
  induction m with
  | zero => simpa using upper_one (F := F) (n := n)
  | succ m ih => rw [pow_succ];exact upper_mul ih hA

theorem upper_pow_diag {A : SpecialLinearGroup (Fin n) F} (hA : Upper A)
    (m : ℕ) (i : Fin n) : (A^m).val i i = A.val i i ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,upper_mul_diag (upper_pow hA m) hA i,ih,pow_succ]

/-- Any actual upper triangular p-power-order SL matrix in defining
characteristic has diagonal one, by the Frobenius power identity. -/
theorem unitriangular_of_p_power (p : ℕ) [Fact p.Prime] [CharP F p]
    (A : SpecialLinearGroup (Fin n) F) (hA : Upper A) (m : ℕ) (hp : A^(p^m)=1) :
    A ∈ Uplus n F := by
  refine ⟨hA,?_⟩
  intro i
  have he : A.val i i ^ (p^m)=1 := by
    rw [← upper_pow_diag hA, hp];simp
  have hz : (A.val i i-1)^(p^m)=0 := by
    rw [sub_pow_char_pow,he,one_pow,sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)

variable [Finite F]

/-- Actual positive unitary U is maximal among p-subgroups. The proof uses
its proved intrinsic normalizer and the native normalizer condition for
finite p-groups; it assumes neither the unitary group order nor an index. -/
theorem positiveU_maximal (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (Q : Subgroup (specialUnitary n ι)) (hQ : IsPGroup p Q)
    (hU : positiveU n ι  ≤  Q) : Q=positiveU n ι := by
  letI := hQ.isNilpotent
  let H := (positiveU n ι).subgroupOf Q
  have hn : Subgroup.normalizer (H : Set Q)=H := by
    apply le_antisymm ?_ (Subgroup.le_normalizer)
    intro x hx
    have hx' : x.val ∈ Subgroup.normalizer (positiveU n ι : Set (specialUnitary n ι)) := by
      have he := Subgroup.subgroupOf_normalizer_eq hU
      rw [←he] at hx
      exact hx
    have ht := upper_of_normalizer ι hinv hne x.val hx'
    obtain ⟨m,hm⟩ := hQ.exists_pow_pow_eq_one x
    have hm' : x.val.val^(p^m)=1 := congrArg (fun a : Q => a.val.val) hm
    exact unitriangular_of_p_power p x.val.val ht m hm'
  have htop : H=⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent) H hn
  apply le_antisymm ?_ hU
  intro x hx
  have he : (⟨x,hx⟩ : Q) ∈ H := by rw [htop];trivial
  exact he

/-- Genuine native Sylow with exactly the actual positive-unitriangular SU carrier. -/
noncomputable def positiveUSylow (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    Sylow p (specialUnitary n ι) := by
  classical
  letI := Fintype.ofFinite F
  exact {toSubgroup := positiveU n ι
         isPGroup' := positiveU_isPGroup p n ι
         is_maximal' := fun {Q} hQ hU => positiveU_maximal p n ι hinv hne Q hQ hU}

theorem positiveUSylow_toSubgroup (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    (positiveUSylow p n ι hinv hne).toSubgroup = positiveU n ι := rfl

theorem exists_positiveU_sylow (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (ι : RingAut F) (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F) :
    ∃ P : Sylow p (specialUnitary n ι), P.toSubgroup = positiveU n ι :=
  ⟨positiveUSylow p n ι hinv hne,rfl⟩

end NikolovSegal.UnitarySylow
