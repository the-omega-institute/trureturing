/- GID: D5/S3/Combinatorics/Matroids/CircuitCoefficientExchange
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/CircuitCoefficientExchange
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: An integral involution exchanges one coefficient sector between two forms. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitPassiveCoordinates

/-! Exchange of coefficient sectors by an integral linear involution. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.CircuitCoefficientExchange

open Finset UniformCircuitResidueForms CircuitPassiveCoordinates

set_option autoImplicit false

/-- One coefficient can be imposed jointly or separately from a family of
coefficients in other sectors. Exchanging just its sector gives the
equivalence of products. -/
theorem coefficient_family_exchange {I M N : Type*} [LinearOrder I]
    [AddCommGroup M] [AddCommGroup N] {d : ℕ}
    (b : Module.Basis I ℤ M) (A : Finset I)
    (K : Submodule ℤ (M [⋀^Fin d]→ₗ[ℤ] N))
    (F : Set.powersetCard I d) (previous : Finset (Set.powersetCard I d))
    (hK : ∀ f : K, project b A (F.val ∩ A) f.val ∈ K)
    (hsep : ∀ G ∈ previous, G.val ∩ A ≠ F.val ∩ A) :
    let read := fun G : Set.powersetCard I d =>
      (LinearMap.proj G).comp ((basisFormEquiv (N := N) b).symm.toLinearMap.comp K.subtype)
    let old := ⨅ G : previous, (read G.val).ker
    let new := (read F).ker
    Nonempty ((↥K × ↥(old ⊓ new)) ≃ₗ[ℤ] (↥old × ↥new)) := by
  classical
  intro read old new
  let P : K →ₗ[ℤ] K := ((project b A (F.val ∩ A)).comp K.subtype).codRestrict K hK
  let Q : K →ₗ[ℤ] K := LinearMap.id - P
  have readP (G : Set.powersetCard I d) (f : K) : read G (P f) =
      if G.val ∩ A = F.val ∩ A then read G f else 0 := by
    change (basisFormEquiv b).symm (project b A (F.val ∩ A) f.val) G = _
    simp [project, read]
  let first : K × K →ₗ[ℤ] K := LinearMap.fst ℤ K K
  let second : K × K →ₗ[ℤ] K := LinearMap.snd ℤ K K
  let exchange := (P.comp first + Q.comp second).prod (Q.comp first + P.comp second)
  have reads (G : Set.powersetCard I d) (x : K × K) :
      read G (exchange x).1 =
        (if G.val ∩ A = F.val ∩ A then read G x.1 else read G x.2) ∧
      read G (exchange x).2 =
        (if G.val ∩ A = F.val ∩ A then read G x.2 else read G x.1) := by
    change read G (P x.1 + (x.2 - P x.2)) = _ ∧
      read G ((x.1 - P x.1) + P x.2) = _
    simp only [map_add, map_sub, readP]
    split_ifs <;> simp
  have ext_read (f g : K) (h : ∀ G, read G f = read G g) : f = g := by
    apply Subtype.ext
    exact (basisFormEquiv b).symm.injective (funext h)
  have exchange_twice : Function.Involutive exchange := by
    intro x
    apply Prod.ext <;> apply ext_read <;> intro G
    · rw [(reads G (exchange x)).1, (reads G x).1, (reads G x).2]
      split_ifs <;> rfl
    · rw [(reads G (exchange x)).2, (reads G x).2, (reads G x).1]
      split_ifs <;> rfl
  have mem_old (f : K) : f ∈ old ↔ ∀ G : previous, read G.val f = 0 := by
    simp only [old, Submodule.mem_iInf, LinearMap.mem_ker]
  have hmem (x : K × K) : x.2 ∈ old ⊓ new ↔ (exchange x).1 ∈ old ∧ (exchange x).2 ∈ new := by
    change (x.2 ∈ old ∧ read F x.2 = 0) ↔
      (exchange x).1 ∈ old ∧ read F (exchange x).2 = 0
    rw [mem_old, mem_old, (reads F x).2, ite_eq_left rfl]
    have read_old (G : previous) : read G.val (exchange x).1 = read G.val x.2 :=
      (reads G.val x).1.trans (ite_eq_right (hsep G.val G.prop))
    simp only [read_old]
  let e := LinearEquiv.ofInvolutive exchange exchange_twice
  let domain := (⊤ : Submodule ℤ K).prod (old ⊓ new)
  let target := old.prod new
  have htarget : domain.map e.toLinearMap = target := by
    ext x
    simp only [domain, target, Submodule.mem_map, Submodule.mem_prod, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
    · intro hx
      refine ⟨exchange x, (hmem (exchange x)).mpr ?_, exchange_twice x⟩
      rw [exchange_twice x]
      exact hx
  let topEquiv : (⊤ : Submodule ℤ K) ≃ₗ[ℤ] K := Submodule.topEquiv
  let start := topEquiv.symm.prodCongr (LinearEquiv.refl ℤ ↥(old ⊓ new))
  exact ⟨start.trans ((Submodule.prodEquiv ⊤ (old ⊓ new)).symm.trans
    ((e.ofSubmodules domain target htarget).trans (Submodule.prodEquiv old new)))⟩

end D5.S3.Combinatorics.Matroids.CircuitCoefficientExchange
