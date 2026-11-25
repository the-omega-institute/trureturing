/- GID: D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CommonPivotOmissionExchange
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Exchange of sparse omitted coefficients at a common pivot. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitReplacementSupport
public import D5.S3.Combinatorics.Matroids.PrimePowerPivotBasis


import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Int.Basic

/-! Exchange of omission constraints at a common pivot over a primary component. -/


@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CommonPivotOmissionExchange

open Finset
open scoped Classical
open D5.S3.Combinatorics.Matroids.UniformCircuitResidueForms
open CircuitReplacementSupport PrimePowerPivotBasis

/-- Exchange the projection part between two elements. The projection lies
in the old kernel, and the complementary projection lies in the new kernel. -/
private theorem exchange_of_projection {K : Type*} [AddCommGroup K]
    (old new : Submodule ℤ K) (P : K →ₗ[ℤ] K)
    (hid : ∀ x, P (P x) = P x)
    (hold : ∀ x, P x ∈ old)
    (hnew : ∀ x, x - P x ∈ new) :
    Nonempty ((K × ↥(old ⊓ new)) ≃ₗ[ℤ] (↥old × ↥new)) := by
  let Q : K →ₗ[ℤ] K := LinearMap.id - P
  let a : K × K →ₗ[ℤ] K := LinearMap.fst ℤ K K
  let b : K × K →ₗ[ℤ] K := LinearMap.snd ℤ K K
  let exchange := (P.comp a + Q.comp b).prod (Q.comp a + P.comp b)
  have exchange_first (x : K × K) : (exchange x).1 = P x.1 + (x.2 - P x.2) := rfl
  have exchange_second (x : K × K) : (exchange x).2 = x.1 - P x.1 + P x.2 := rfl
  have involutive : Function.Involutive exchange := by
    intro x
    apply Prod.ext
    · rw [exchange_first, exchange_first, exchange_second]
      simp only [map_add, map_sub, hid]
      abel
    · rw [exchange_second, exchange_first, exchange_second]
      simp only [map_add, map_sub, hid]
      abel
  have old_iff (x : K × K) : (exchange x).1 ∈ old ↔ x.2 ∈ old := by
    rw [exchange_first]
    constructor
    · intro h
      have h' : x.2 - P x.2 ∈ old := by
        convert old.sub_mem h (hold x.1) using 1 <;> abel
      simpa using old.add_mem h' (hold x.2)
    · intro h
      exact old.add_mem (hold x.1) (old.sub_mem h (hold x.2))
  have new_iff (x : K × K) : (exchange x).2 ∈ new ↔ x.2 ∈ new := by
    rw [exchange_second]
    constructor
    · intro h
      have h' : P x.2 ∈ new := by
        convert new.sub_mem h (hnew x.1) using 1 <;> abel
      simpa using new.add_mem (hnew x.2) h'
    · intro h
      have h' : P x.2 ∈ new := by
        simpa using new.sub_mem h (hnew x.2)
      exact new.add_mem (hnew x.1) h'
  let e := LinearEquiv.ofInvolutive exchange involutive
  let domain := (⊤ : Submodule ℤ K).prod (old ⊓ new)
  let target := old.prod new
  have hmap : domain.map e.toLinearMap = target := by
    ext x
    simp only [domain, target, Submodule.mem_map, Submodule.mem_prod, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(old_iff y).mpr hy.1, (new_iff y).mpr hy.2⟩
    · rintro ⟨hx₁, hx₂⟩
      have h₁ : (exchange (exchange x)).1 ∈ old := by rw [involutive x]; exact hx₁
      have h₂ : (exchange (exchange x)).2 ∈ new := by rw [involutive x]; exact hx₂
      exact ⟨exchange x, ⟨(old_iff (exchange x)).mp h₁,
        (new_iff (exchange x)).mp h₂⟩, involutive x⟩
  let topEquiv : (⊤ : Submodule ℤ K) ≃ₗ[ℤ] K := Submodule.topEquiv
  exact ⟨(topEquiv.symm.prodCongr (LinearEquiv.refl ℤ ↥(old ⊓ new))).trans
    ((Submodule.prodEquiv ⊤ (old ⊓ new)).symm.trans
      ((e.ofSubmodules domain target hmap).trans (Submodule.prodEquiv old new)))⟩


/-- A module killed by the product of two coprime integers splits into the two
corresponding torsion submodules. -/
private theorem coprimeSplit {M : Type*} [AddCommGroup M] {m n : ℤ}
    (hcoprime : IsCoprime m n) (hkill : ∀ x : M, (m * n) • x = 0) :
    Nonempty (M ≃ₗ[ℤ] (Submodule.torsionBy ℤ M m × Submodule.torsionBy ℤ M n)) := by
  obtain ⟨a, b, hab⟩ := hcoprime
  have hsum (x : M) : (b * n) • x + (a * m) • x = x := by
    rw [← add_smul, add_comm, hab, one_smul]
  have hdis : IsCompl (Submodule.torsionBy ℤ M m) (Submodule.torsionBy ℤ M n) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hm hn
      have hm' : m • x = 0 := hm
      have hn' : n • x = 0 := hn
      have h := hsum x
      rw [mul_smul, mul_smul, hn', hm', smul_zero, smul_zero, add_zero] at h
      exact h.symm
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hleft : (b * n) • x ∈ Submodule.torsionBy ℤ M m := by
        rw [Submodule.mem_torsionBy_iff, ← mul_smul,
          show m * (b * n) = b * (m * n) by ring, mul_smul, hkill, smul_zero]
      have hright : (a * m) • x ∈ Submodule.torsionBy ℤ M n := by
        rw [Submodule.mem_torsionBy_iff, ← mul_smul,
          show n * (a * m) = a * (m * n) by ring, mul_smul, hkill, smul_zero]
      exact hsum x ▸ Submodule.add_mem_sup hleft hright
  exact ⟨(Submodule.prodEquivOfIsCompl _ _ hdis).symm⟩

private abbrev constrained {M : Type*} [AddCommGroup M] (K : Submodule ℤ M) (a : ℤ) :=
  K ⊓ Submodule.torsionBy ℤ M a

private def nestedTorsion {M : Type*} [AddCommGroup M] (K : Submodule ℤ M)
    {a b : ℤ} (hdvd : a ∣ b) :
    Submodule.torsionBy ℤ (constrained K b) a ≃ₗ[ℤ] constrained K a where
  toFun x := ⟨x.val.val, x.val.prop.1, congrArg Subtype.val x.prop⟩
  invFun x :=
    ⟨⟨x.val, x.prop.1, by
      obtain ⟨c, rfl⟩ := hdvd
      change (a * c) • x.val = 0
      rw [mul_comm, mul_smul, show a • x.val = 0 from x.prop.2, smul_zero]⟩,
    Subtype.ext x.prop.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := rfl
  map_smul' c x := rfl

/-- Coprime integer torsion splits even after imposing a common linear constraint. -/
private theorem constrained_coprime_split {M : Type*} [AddCommGroup M] (K : Submodule ℤ M)
    {m n : ℤ} (h : IsCoprime m n) :
    Nonempty (↥(K ⊓ Submodule.torsionBy ℤ M (m * n)) ≃ₗ[ℤ]
      (↥(K ⊓ Submodule.torsionBy ℤ M m) × ↥(K ⊓ Submodule.torsionBy ℤ M n))) := by
  obtain ⟨e⟩ := coprimeSplit h
    (M := constrained K (m * n)) (fun x => Subtype.ext x.prop.2)
  exact ⟨e.trans ((nestedTorsion K (dvd_mul_right m n)).prodCongr
    (nestedTorsion K (dvd_mul_left n m)))⟩



/-- The part of an additive submodule killed by a specified integer. -/
private abbrev AtTorsion {M : Type*} [AddCommGroup M] (K : Submodule ℤ M) (a : ℕ) :=
  K ⊓ Submodule.torsionBy ℤ M (a : ℤ)

/-- A product identity valid at all positive prime powers holds at every
positive modulus. Each of the four submodules is fixed before splitting. -/
private theorem recombine_torsion_products {M : Type*} [AddCommGroup M]
    (A B C D : Submodule ℤ M)
    (primary : ∀ (p k : ℕ), p.Prime → 0 < k →
      Nonempty ((AtTorsion A (p ^ k) × AtTorsion B (p ^ k)) ≃ₗ[ℤ]
        (AtTorsion C (p ^ k) × AtTorsion D (p ^ k))))
    (a : ℕ) (ha : a ≠ 0) :
    Nonempty ((AtTorsion A a × AtTorsion B a) ≃ₗ[ℤ] (AtTorsion C a × AtTorsion D a)) := by
  induction a using Nat.recOnPosPrimePosCoprime with
  | zero => exact (ha rfl).elim
  | one =>
    have subs (K : Submodule ℤ M) : Subsingleton (AtTorsion K 1) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx : (1 : ℤ) • x.val = 0 := x.prop.2
      have hy : (1 : ℤ) • y.val = 0 := y.prop.2
      rw [one_smul] at hx hy
      rw [hx, hy]
    letI := subs A
    letI := subs B
    letI := subs C
    letI := subs D
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | prime_pow p k hp hk => exact primary p k hp hk
  | coprime m n hm hn hc ih₁ ih₂ =>
    have hc' : IsCoprime (m : ℤ) (n : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hc)
    have split (K : Submodule ℤ M) :
        Nonempty ((AtTorsion K (m * n)) ≃ₗ[ℤ] (AtTorsion K m × AtTorsion K n)) := by
      change Nonempty (↥(K ⊓ Submodule.torsionBy ℤ M ((m * n : ℕ) : ℤ)) ≃ₗ[ℤ]
        (↥(K ⊓ Submodule.torsionBy ℤ M (m : ℤ)) × ↥(K ⊓ Submodule.torsionBy ℤ M (n : ℤ))))
      rw [Nat.cast_mul]
      exact constrained_coprime_split K hc'
    obtain ⟨sa⟩ := split A
    obtain ⟨sb⟩ := split B
    obtain ⟨sc⟩ := split C
    obtain ⟨sd⟩ := split D
    obtain ⟨e₁⟩ := ih₁ (by omega)
    obtain ⟨e₂⟩ := ih₂ (by omega)
    exact ⟨(sa.prodCongr sb).trans
      ((LinearEquiv.prodProdProdComm ℤ _ _ _ _).trans
        ((e₁.prodCongr e₂).trans
          ((LinearEquiv.prodProdProdComm ℤ _ _ _ _).trans (sc.prodCongr sd).symm)))⟩


abbrev kernel {M N : Type*} [AddCommGroup M] [AddCommGroup N] {d : ℕ}
    (r y : M) (m : ℤ) : Submodule ℤ (M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :=
  ((insertVector (n := d) (N := N) r).ker ⊓ (insertVector y).ker) ⊓
    Submodule.torsionBy ℤ _ m

private noncomputable def cut {I M N : Type*} [LinearOrder I] [AddCommGroup M] [AddCommGroup N]
    {k : ℕ} (b : Module.Basis I ℤ M) (S : Set (Finset I)) :
    (M [⋀^Fin k]→ₗ[ℤ] N) →ₗ[ℤ] M [⋀^Fin k]→ₗ[ℤ] N := by
  classical
  let e := basisFormEquiv (N := N) (n := k) b
  let mask : (Set.powersetCard I k → N) →ₗ[ℤ] (Set.powersetCard I k → N) := {
    toFun := fun f (G : Set.powersetCard I k) => if G.val ∈ S then f G else 0
    map_add' := fun f g => by ext H; by_cases hh : H.val ∈ S <;> simp [hh]
    map_smul' := fun a f => by ext H; by_cases hh : H.val ∈ S <;> simp [hh]
    }
  exact e.toLinearMap.comp (mask.comp e.symm.toLinearMap)

private theorem cut_coordinate {I M N : Type*} [LinearOrder I]
    [AddCommGroup M] [AddCommGroup N] {k : ℕ} (b : Module.Basis I ℤ M)
    (S : Set (Finset I)) (f : M [⋀^Fin k]→ₗ[ℤ] N) (G : Set.powersetCard I k) :
    (basisFormEquiv b).symm (cut b S f) G =
      if G.val ∈ S then (basisFormEquiv b).symm f G else 0 := by
  classical
  simp [cut]

private theorem primary_omission_exchange {I M N : Type*} [LinearOrder I] [Fintype I] [Nonempty I]
    [AddCommGroup M] [AddCommGroup N] {d : ℕ} (b : Module.Basis I ℤ M)
    (root : I) (w : I → ℕ) (hweight : ∃ i ≠ root, w i ≠ 0)
    {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (F : Set.powersetCard I (d + 1))
    (previous : Finset (Set.powersetCard I (d + 1)))
    (hsep : ∀ G ∈ previous, (F.val ∩ G.val).card + 2 ≤ d + 1) :
    let K := kernel (N := N) (d := d) (b root) (∑ i, (w i : ℤ) • b i) ((p ^ a : ℕ) : ℤ)
    let read := fun G : Set.powersetCard I (d + 1) =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    let new := (read F).ker
    Nonempty ((K × ↥(old ⊓ new)) ≃ₗ[ℤ] (↥old × ↥new)) := by
  classical
  intro K read old new
  let w₀ (i : I) := if i = root then 0 else w i
  have hw₀ : ∃ i, w₀ i ≠ 0 := by
    obtain ⟨i, hi, hw⟩ := hweight
    exact ⟨i, by simpa [w₀, hi] using hw⟩
  obtain ⟨x, c, z, hx, hchange, hz⟩ := primary_pivot_basis b w₀ hw₀ hp ha
  have hxroot : x ≠ root := by intro h; subst x; simp [w₀] at hx
  have hroot : c root = b root := hchange root (Ne.symm hxroot)
  let m : ℤ := ((p ^ a : ℕ) : ℤ)
  let y : M := ∑ i, (w i : ℤ) • b i
  let y₀ : M := ∑ i, (w₀ i : ℤ) • b i
  let t : ℤ := (w₀ x : ℤ)
  have hy : y = y₀ + (w root : ℤ) • b root := by
    rw [show y = ∑ i, (w i : ℤ) • b i from rfl,
      show y₀ = ∑ i, (w₀ i : ℤ) • b i from rfl]
    rw [← Finset.sum_erase_add _ _ (mem_univ root), ← Finset.sum_erase_add _ _ (mem_univ root)]
    simp only [w₀, if_pos rfl, Int.natCast_zero, zero_smul, add_zero]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [w₀, ne_of_mem_erase hi]
  have hy₀ : y₀ = t • c x - m • z := by
    change t • c x - y₀ = m • z at hz
    rw [← hz]
    abel
  have insert_mul (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) (h : m • f = 0) :
      f.curryLeft (m • z) = 0 := by
    ext v
    have hv := congrArg (fun g : M [⋀^Fin (d + 1)]→ₗ[ℤ] N => g (Matrix.vecCons z v)) h
    simpa [AlternatingMap.curryLeft_apply_apply] using hv
  have hform (f : M [⋀^Fin (d + 1)]→ₗ[ℤ] N) :
      f ∈ K ↔ (f.curryLeft (c root) = 0 ∧ f.curryLeft (t • c x) = 0) ∧ m • f = 0 := by
    change ((f.curryLeft (b root) = 0 ∧ f.curryLeft y = 0) ∧ m • f = 0) ↔ _
    rw [hroot]
    constructor <;> rintro ⟨⟨hr, hy₁⟩, htor⟩ <;> refine ⟨⟨hr, ?_⟩, htor⟩
    · simp only [hy, hy₀, map_add, map_sub, map_zsmul, hr, smul_zero, add_zero,
        insert_mul f htor, sub_zero] at hy₁
      simpa only [map_zsmul] using hy₁
    · simpa only [hy, hy₀, map_add, map_sub, map_zsmul, hr, smul_zero, add_zero,
        insert_mul f htor, sub_zero] using hy₁
  let S := oldCoordinateSupport x F.val
  have hcK (f : K) : cut c S f.val ∈ K := by
    obtain ⟨⟨hr, hw⟩, htor⟩ := (hform f.val).mp f.prop
    refine (hform _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← one_smul ℤ (c root), curryLeft_smul_basis_eq_zero_iff]
      intro G hG
      rw [cut_coordinate]
      have hv := (curryLeft_smul_basis_eq_zero_iff c f.val 1 root).mp (by simpa using hr) G hG
      split_ifs <;> simp_all
    · rw [curryLeft_smul_basis_eq_zero_iff]
      intro G hG
      rw [cut_coordinate]
      have hv := (curryLeft_smul_basis_eq_zero_iff c f.val t x).mp hw G hG
      split_ifs <;> simp_all
    · rw [← map_zsmul, htor, map_zero]
  let P : K →ₗ[ℤ] K := ((cut c S).comp K.subtype).codRestrict K hcK
  have hid (f : K) : P (P f) = P f := by
    apply Subtype.ext
    apply (basisFormEquiv c).symm.injective
    funext G
    change (basisFormEquiv c).symm (cut c S (cut c S f.val)) G =
      (basisFormEquiv c).symm (cut c S f.val) G
    simp only [cut_coordinate]
    split_ifs <;> rfl
  have hold (f : K) : P f ∈ old := by
    rw [show old = ⨅ G : previous, (read G.val).ker from rfl, Submodule.mem_iInf]
    intro G
    change (basisFormEquiv b).symm (cut c S f.val) G.val = 0
    apply old_coordinate_zero_of_replacement_support b c x hchange
    intro T hT
    rw [cut_coordinate]
    have hcard : F.val.card = G.val.val.card := F.prop.trans G.val.prop.symm
    have hsep' : (F.val ∩ G.val.val).card + 2 ≤ F.val.card :=
      (hsep G.val G.prop).trans F.prop.ge
    have hout : T.val ∉ S :=
      fun h => Set.disjoint_left.mp (disjoint_old_coordinate_support x hcard hsep') h hT
    simp [hout]
  have hnew (f : K) : f - P f ∈ new := by
    change (basisFormEquiv b).symm (f.val - cut c S f.val) F = 0
    apply old_coordinate_zero_of_replacement_support b c x hchange
    intro G hG
    rw [map_sub]
    change (basisFormEquiv c).symm f.val G - (basisFormEquiv c).symm (cut c S f.val) G = 0
    rw [cut_coordinate, if_pos (show G.val ∈ S from hG), sub_self]
  exact exchange_of_projection old new P hid hold hnew


private def restrictTo {T : Type*} [AddCommGroup T] (K Q : Submodule ℤ T) :
    ↥(Q.comap K.subtype) ≃ₗ[ℤ] ↥(K ⊓ Q) where
  toFun x := ⟨x.val.val, x.val.prop, x.prop⟩
  invFun x := ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

theorem common_pivot_omission_exchange {I M N : Type*}
    [LinearOrder I] [Fintype I] [Nonempty I] [AddCommGroup M] [AddCommGroup N]
    {d : ℕ} (b : Module.Basis I ℤ M) (root : I) (w : I → ℕ)
    (hweight : ∃ i ≠ root, w i ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (F : Set.powersetCard I (d + 1)) (previous : Finset (Set.powersetCard I (d + 1)))
    (hsep : ∀ G ∈ previous, (F.val ∩ G.val).card + 2 ≤ d + 1) :
    let K := kernel (N := N) (d := d) (b root) (∑ i, (w i : ℤ) • b i) (n : ℤ)
    let read := fun G : Set.powersetCard I (d + 1) =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    let new := (read F).ker
    Nonempty ((K × ↥(old ⊓ new)) ≃ₗ[ℤ] (↥old × ↥new)) := by
  intro K read old new
  let T := M [⋀^Fin (d + 1)]→ₗ[ℤ] N
  let B : Submodule ℤ T :=
    (insertVector (n := d) (N := N) (b root)).ker ⊓
    (insertVector (∑ i, (w i : ℤ) • b i)).ker
  let raw (G : Set.powersetCard I (d + 1)) : T →ₗ[ℤ] N :=
    (LinearMap.proj G).comp (basisFormEquiv b).symm.toLinearMap
  let O : Submodule ℤ T := ⨅ G : previous, (raw G.val).ker
  let P : Submodule ℤ T := (raw F).ker
  let left (a : ℕ) := (AtTorsion B a) × (AtTorsion (B ⊓ (O ⊓ P)) a)
  let right (a : ℕ) := (AtTorsion (B ⊓ O) a) × (AtTorsion (B ⊓ P) a)
  have pairEquiv (a : ℕ) (Q : Submodule ℤ T) :
      ↥(Q.comap (AtTorsion B a).subtype) ≃ₗ[ℤ] ↥(AtTorsion (B ⊓ Q) a) := by
    have hs : AtTorsion B a ⊓ Q = AtTorsion (B ⊓ Q) a := by
      change (B ⊓ Submodule.torsionBy ℤ T (a : ℤ)) ⊓ Q =
        (B ⊓ Q) ⊓ Submodule.torsionBy ℤ T (a : ℤ)
      rw [inf_right_comm]
    exact (restrictTo (AtTorsion B a) Q).trans (LinearEquiv.ofEq _ _ hs)
  have leftEquiv (a : ℕ) :
      (AtTorsion B a × ↥(O.comap (AtTorsion B a).subtype ⊓
        P.comap (AtTorsion B a).subtype)) ≃ₗ[ℤ] left a := by
    rw [← Submodule.comap_inf]
    exact (LinearEquiv.refl ℤ _).prodCongr (pairEquiv a (O ⊓ P))
  have rightEquiv (a : ℕ) :
      (↥(O.comap (AtTorsion B a).subtype) × ↥(P.comap (AtTorsion B a).subtype)) ≃ₗ[ℤ]
        right a :=
    (pairEquiv a O).prodCongr (pairEquiv a P)
  have co_old (a : ℕ) :
      O.comap (AtTorsion B a).subtype = ⨅ G : previous,
        ((raw G.val).comp (AtTorsion B a).subtype).ker := by
    ext f
    simp only [O, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.comp_apply]
  have co_new (a : ℕ) :
      P.comap (AtTorsion B a).subtype = ((raw F).comp (AtTorsion B a).subtype).ker := by
    ext f
    rfl
  have primary (p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
      Nonempty ((left (p ^ a)) ≃ₗ[ℤ] (right (p ^ a))) := by
    obtain ⟨e⟩ := primary_omission_exchange (N := N) b root w hweight hp ha F previous hsep
    have e' : (AtTorsion B (p ^ a) × ↥(O.comap (AtTorsion B (p ^ a)).subtype ⊓
        P.comap (AtTorsion B (p ^ a)).subtype)) ≃ₗ[ℤ]
      (↥(O.comap (AtTorsion B (p ^ a)).subtype) ×
        ↥(P.comap (AtTorsion B (p ^ a)).subtype)) := by
      rw [co_old, co_new]
      exact e
    exact ⟨(leftEquiv _).symm.trans (e'.trans (rightEquiv _))⟩
  obtain ⟨e⟩ := recombine_torsion_products B (B ⊓ (O ⊓ P)) (B ⊓ O) (B ⊓ P) primary n hn
  have old_eq : old = O.comap (AtTorsion B n).subtype := by rw [co_old]; rfl
  have new_eq : new = P.comap (AtTorsion B n).subtype := by rw [co_new]; rfl
  rw [old_eq, new_eq]
  exact ⟨(leftEquiv n).trans (e.trans (rightEquiv n).symm)⟩


end D5.S3.Combinatorics.Matroids.CommonPivotOmissionExchange
