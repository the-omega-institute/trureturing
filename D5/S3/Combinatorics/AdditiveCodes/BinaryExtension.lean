/- GID: D5/S3/Combinatorics/AdditiveCodes/BinaryExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/AdditiveCodes/BinaryExtension
   mirror-E: none(waiver:alderson-binary-problem-resolution)
   anchors: []
   utility: none
   digest: Binary extendable additively maximal codes exist exactly for message dimension k ≥ 2. -/

import D5.S3.Combinatorics.AdditiveCodes.AdditiveCodesBinaryLift
import D5.S3.Combinatorics.AdditiveCodes.AdditiveCodesWeighting

set_option autoImplicit false

namespace D5.S3.Combinatorics.AdditiveCodes.BinaryExtension

open AdditiveExtensionDefs Module

/-- Alderson's Problem 9.3 for the binary base field and every alphabet dimension at least three. -/
theorem result : AdditiveExtensionDefs.claimBinary := by
  classical
  have kOne_has_additiveExtension {F : Type} [Field F] [Fintype F] [DecidableEq F]
      {m n d : ℕ} (C : Finset (Fin n → Fin m → F))
      (hC : IsCode C 1 d) (hadd : IsAdditive C) :
      ∃ D, IsExtension C D 1 d ∧ IsAdditive D := by
    classical
    obtain ⟨S, hS⟩ := hadd
    have memS (x : Fin n → Fin m → F) : x ∈ S ↔ x ∈ C := Set.ext_iff.mp hS x
    let supportEquiv : S ≃ {x // x ∈ C} :=
      { toFun := fun x => ⟨x, (memS _).mp x.property⟩
        invFun := fun x => ⟨x, (memS _).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have cardeq : Fintype.card S = Fintype.card (Fin m → F) := by
      rw [Fintype.card_congr supportEquiv]
      simpa only [Fintype.card_coe, pow_one, Nat.card_eq_fintype_card] using hC.2.1
    have dim : Module.finrank F S = Module.finrank F (Fin m → F) := by
      apply Nat.pow_right_injective (a := Fintype.card F)
        (by have := Fintype.one_lt_card (α := F); omega)
      simpa only [← Module.card_eq_pow_finrank] using cardeq
    let label : S ≃ₗ[F] (Fin m → F) := LinearEquiv.ofFinrankEq S (Fin m → F) dim
    let G : S →ₗ[F] (Fin (n + 1) → Fin m → F) :=
      { toFun := fun x => Fin.snoc x.val (label x)
        map_add' := by
          intro x y
          ext i j
          refine Fin.lastCases ?_ (fun t => ?_) i
          · simp [Fin.snoc_last]
          · simp [Fin.snoc_castSucc]
        map_smul' := by
          intro a x
          ext i j
          refine Fin.lastCases ?_ (fun t => ?_) i
          · simp [Fin.snoc_last]
          · simp [Fin.snoc_castSucc] }
    have original : Finset.univ.image (fun x : S => x.val) = C := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists,
        exists_prop, exists_eq_right]
      exact memS x
    let D := Finset.univ.image G
    have extension : IsExtension C D 1 d := by
      rw [← original]
      let E : S → Fin n → Fin m → F := fun x => x.val
      have hE : Function.Injective E := Subtype.val_injective
      have hCgraph : IsCode (Finset.univ.image E) 1 d := by
        simpa only [E, original] using hC
      have hlabel : ∀ x y : S, x ≠ y → hammingDist (E x) (E y) = d →
          label x ≠ label y := fun _ _ hxy _ => label.injective.ne hxy
      let G : S → Fin (n + 1) → Fin m → F := fun x => Fin.snoc (E x) (label x)
      have hG : Function.Injective G := by
        intro x y h
        apply hE
        simpa [G] using congrArg Fin.init h
      have distance (x y : S) : hammingDist (G x) (G y) =
          hammingDist (E x) (E y) + if label x = label y then 0 else 1 := by
        simp only [hammingDist, Finset.card_filter, Fin.sum_univ_castSucc,
          G, Fin.snoc_castSucc, Fin.snoc_last]
        by_cases h : label x = label y <;> simp [h]
      change IsExtension (Finset.univ.image E) (Finset.univ.image G) 1 d
      refine ⟨hCgraph, ⟨Nat.le_trans hCgraph.1 (Nat.le_succ n), ?_, ?_⟩, ?_⟩
      · rw [Finset.card_image_of_injective _ hG]
        simpa only [Finset.card_image_of_injective _ hE] using hCgraph.2.1
      · constructor
        · intro a ha b hb hab
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
          have hxy : x ≠ y := fun h => hab (congrArg G h)
          have old := hCgraph.2.2.1 (E x) (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
            (E y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩) (hE.ne hxy)
          rw [distance]
          by_cases heq : hammingDist (E x) (E y) = d
          · simp [hlabel x y hxy heq, heq]
          · split_ifs <;> omega
        · obtain ⟨a, ha, b, hb, hab, hd⟩ := hCgraph.2.2.2
          obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
          have hxy : x ≠ y := fun h => hab (congrArg E h)
          refine ⟨G x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩,
            G y, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩, hG.ne hxy, ?_⟩
          rw [distance]
          simp [hlabel x y hxy hd, hd]
      · ext w
        simp [G, E, Finset.mem_image, Fin.init_snoc]
    
    refine ⟨D, extension, G.range, ?_⟩
    ext z
    change (∃ x, G x = z) ↔ z ∈ D
    simp only [D, Finset.mem_image, Finset.mem_univ, true_and]
  intro m hm k hk
  constructor
  · rintro ⟨n, d, C, hC, hadd, _, hmax⟩
    by_contra hk2
    have hk1 : k = 1 := by omega
    subst k
    exact hmax (kOne_has_additiveExtension C hC hadd)
  · intro hk2
    let r := m * (k - 1)
    let a := r - 3
    let b := m - 3
    let V := (Fin 6 → ZMod 2) × (Fin a → ZMod 2) × (Fin b → ZMod 2)
    have hks : k = (k - 1) + 1 := by omega
    have hkprev : 1 ≤ k - 1 := by omega
    have hrm : r + m = k * m := by dsimp [r]; nlinarith
    have hr3 : 3 ≤ r := by dsimp [r]; nlinarith
    have hdim : finrank (ZMod 2) V = k * m := by
      simp only [V, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
      dsimp [a, b]
      omega
    obtain ⟨B, hB, _, block, label, avoid⟩ := binaryLift a b
    let alphabet : ((Fin 3 → ZMod 2) × (Fin b → ZMod 2)) ≃ₗ[ZMod 2]
        (Fin m → ZMod 2) := LinearEquiv.ofFinrankEq _ _ (by
          simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
          dsimp [b]
          omega)
    have hblock : ∀ K : Submodule (ZMod 2) V, finrank (ZMod 2) K = r →
        ∃ P ∈ B, P.submodule ≤ K := by
      intro K hK
      apply block K
      simpa only [a, Nat.sub_add_cancel hr3] using hK
    have hav : ∀ x y : V, (hxy : x ≠ y) → alphabet (label x) = alphabet (label y) →
        Projectivization.mk (ZMod 2) (x - y) (sub_ne_zero.mpr hxy) ∉ B := by
      intro x y hxy heq
      exact avoid x y hxy (alphabet.injective heq)
    have constructed := incidenceConstruction m k r (by omega) (by omega)
      hdim hrm B hB hblock (fun x => alphabet (label x)) hav
    have hdec : (fun x y : ZMod 2 => Classical.propDecidable (x = y)) =
        ZMod.decidableEq 2 := by
      funext x y
      exact Subsingleton.elim _ _
    rw [hdec] at constructed
    exact constructed

end D5.S3.Combinatorics.AdditiveCodes.BinaryExtension
