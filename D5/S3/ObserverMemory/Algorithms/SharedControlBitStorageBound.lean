/- GID: D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared control dynamics force the sharp storage product bound. -/

import Mathlib
import Mathlib.LinearAlgebra.Basis.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound

open Function Set Module

/-- The `i`th control rewrite replaces every data bit except the `i`th by zero,
copies the control bit into the `i`th data coordinate, and clears the control. -/
def controlRewrite {d : ℕ} (i : Fin d) :
    ((Fin d → ZMod 2) × ZMod 2) → ((Fin d → ZMod 2) × ZMod 2) :=
  fun z ↦ (Pi.single i z.2, 0)

/-- The action family consists of the `d` data-basis translations, the control
basis translation, and the `d` control rewrites. -/
def sharedControlActions (d : ℕ) :
    Set ((((Fin d → ZMod 2) × ZMod 2) → ((Fin d → ZMod 2) × ZMod 2))) :=
  {f | (∃ i : Fin d, f = fun z ↦ z + (Pi.single i 1, 0)) ∨
    f = (fun z ↦ z + (0, 1)) ∨ ∃ i : Fin d, f = controlRewrite i}

/-- A code is dynamically closed when every allowed state action descends to
an update of the code value. -/
def DynamicallyClosed {d : ℕ} {α : Type*}
    (u : ((Fin d → ZMod 2) × ZMod 2) → α) : Prop :=
  ∀ f ∈ sharedControlActions d, ∃ F : α → α, u ∘ f = F ∘ u

/-- The code retaining the first `h` data coordinates and the shared control bit. -/
def prefixCode {d h : ℕ} (hd : h ≤ d) :
    ((Fin d → ZMod 2) × ZMod 2) → ((Fin h → ZMod 2) × ZMod 2) :=
  fun z ↦ ((fun i ↦ z.1 (Fin.castLE hd i)), z.2)

/-- The code retaining the last `d - h` data coordinates and the shared control bit. -/
def suffixCode {d h : ℕ} (hd : h ≤ d) :
    ((Fin d → ZMod 2) × ZMod 2) → ((Fin (d - h) → ZMod 2) × ZMod 2) :=
  fun z ↦ ((fun i ↦ z.1 ⟨h + i, by omega⟩), z.2)

/-- Dynamical closure classifies every local kernel, every permitted kernel is
realized by its quotient code, the product lower bound holds for two
noninjective jointly faithful codes, and complementary prefix/suffix codes
attain that bound. -/
theorem shared_control_bit_storage_bound
    (d : ℕ) (hd : 2 ≤ d) {α β : Type} [Finite α] [Finite β]
    (u : ((Fin d → ZMod 2) × ZMod 2) → α)
    (v : ((Fin d → ZMod 2) × ZMod 2) → β)
    (hu : DynamicallyClosed u) (hv : DynamicallyClosed v)
    (hjoint : Injective (fun z ↦ (u z, v z))) :
    (∃ H : Submodule (ZMod 2) ((Fin d → ZMod 2) × ZMod 2),
      (∀ z z', u z = u z' ↔ z - z' ∈ H) ∧
        (H ≤ LinearMap.range
            (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)) ∨ H = ⊤)) ∧
    (∀ H : Submodule (ZMod 2) ((Fin d → ZMod 2) × ZMod 2),
      (H ≤ LinearMap.range
          (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)) ∨ H = ⊤) →
        DynamicallyClosed H.mkQ ∧
          ∀ z z', H.mkQ z = H.mkQ z' ↔ z - z' ∈ H) ∧
    ((¬Injective u ∧ ¬Injective v) →
      2 ^ (d + 2) ≤ (Set.range u).ncard * (Set.range v).ncard) ∧
    ∀ h : ℕ, 1 ≤ h → ∀ hupper : h ≤ d - 1,
      let hle : h ≤ d := hupper.trans (Nat.sub_le d 1)
      DynamicallyClosed (suffixCode hle) ∧
        DynamicallyClosed (prefixCode hle) ∧
        Injective (fun z ↦ (suffixCode hle z, prefixCode hle z)) ∧
        (Set.range (suffixCode hle)).ncard *
            (Set.range (prefixCode hle)).ncard = 2 ^ (d + 2) := by
  classical
  let V := (Fin d → ZMod 2) × ZMod 2
  let W : Submodule (ZMod 2) V :=
    LinearMap.range (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2))
  let stateBasis : Basis (Fin d ⊕ Unit) (ZMod 2) V :=
    (Pi.basisFun (ZMod 2) (Fin d)).prod (Basis.singleton Unit (ZMod 2))
  have stateBasisData (i : Fin d) :
      stateBasis (Sum.inl i) = ((Pi.single i 1, 0) : V) := by
    change ((Pi.basisFun (ZMod 2) (Fin d)).prod
      (Basis.singleton Unit (ZMod 2))) (Sum.inl i) = _
    rw [Module.Basis.prod_apply]
    simp only [Sum.elim_inl, Function.comp_apply, LinearMap.inl_apply,
      Pi.basisFun_apply]
  have stateBasisControl : stateBasis (Sum.inr ()) = ((0, 1) : V) := by
    change ((Pi.basisFun (ZMod 2) (Fin d)).prod
      (Basis.singleton Unit (ZMod 2))) (Sum.inr ()) = _
    rw [Module.Basis.prod_apply]
    simp only [Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply,
      Module.Basis.singleton_apply]
  have kernelData : ∀ {γ : Type} (q : V → γ), DynamicallyClosed q →
      ∃ H : Submodule (ZMod 2) V,
        (∀ z z', q z = q z' ↔ z - z' ∈ H) ∧ (H ≤ W ∨ H = ⊤) := by
    intro γ q hq
    let good : AddSubgroup V :=
      { carrier := {a | ∀ x y, q x = q y → q (x + a) = q (y + a)}
        zero_mem' := by
          intro x y hxy
          simpa using hxy
        add_mem' := by
          intro a b ha hb x y hxy
          have hab := hb (x + a) (y + a) (ha x y hxy)
          simpa only [add_assoc] using hab
        neg_mem' := by
          intro a ha
          simpa only [ZModModule.neg_eq_self] using ha }
    have dataTranslationGood (i : Fin d) : (Pi.single i 1, 0) ∈ good := by
      intro x y hxy
      obtain ⟨F, hF⟩ := hq (fun z ↦ z + (Pi.single i 1, 0))
        (Or.inl ⟨i, rfl⟩)
      calc
        q (x + (Pi.single i 1, 0)) = F (q x) := by
          simpa only [Function.comp_apply] using congrFun hF x
        _ = F (q y) := congrArg F hxy
        _ = q (y + (Pi.single i 1, 0)) := by
          simpa only [Function.comp_apply] using (congrFun hF y).symm
    have controlTranslationGood : (0, 1) ∈ good := by
      intro x y hxy
      obtain ⟨F, hF⟩ := hq (fun z ↦ z + (0, 1)) (Or.inr (Or.inl rfl))
      calc
        q (x + (0, 1)) = F (q x) := by
          simpa only [Function.comp_apply] using congrFun hF x
        _ = F (q y) := congrArg F hxy
        _ = q (y + (0, 1)) := by
          simpa only [Function.comp_apply] using (congrFun hF y).symm
    let goodSub : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 good
    have goodSubTop : goodSub = ⊤ :=
      (Submodule.eq_top_iff_forall_basis_mem stateBasis).2 (by
        intro j
        rcases j with i | j
        · change stateBasis (Sum.inl i) ∈ good
          rw [stateBasisData i]
          exact dataTranslationGood i
        · have hj : j = () := Subsingleton.elim _ _
          subst j
          change stateBasis (Sum.inr ()) ∈ good
          rw [stateBasisControl]
          exact controlTranslationGood)
    have everyTranslationGood (a : V) :
        ∀ x y, q x = q y → q (x + a) = q (y + a) := by
      have ha : a ∈ goodSub := by
        rw [goodSubTop]
        exact Submodule.mem_top
      exact ha
    let kernel : AddSubgroup V :=
      { carrier := {a | q a = q 0}
        zero_mem' := rfl
        add_mem' := by
          intro a b ha hb
          calc
            q (a + b) = q (0 + b) := everyTranslationGood b a 0 ha
            _ = q b := by rw [zero_add]
            _ = q 0 := hb
        neg_mem' := by
          intro a ha
          simpa only [ZModModule.neg_eq_self] using ha }
    let H : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 kernel
    have cosetKernel (z z' : V) : q z = q z' ↔ z - z' ∈ H := by
      constructor
      · intro hzz'
        change q (z - z') = q 0
        have translated := everyTranslationGood (-z') z z' hzz'
        calc
          q (z - z') = q (z' + -z') := by
            simpa only [sub_eq_add_neg] using translated
          _ = q 0 := by rw [add_neg_cancel]
      · intro hdiff
        change q (z - z') = q 0 at hdiff
        have translated := everyTranslationGood z' (z - z') 0 hdiff
        calc
          q z = q ((z - z') + z') := by rw [sub_add_cancel]
          _ = q (0 + z') := translated
          _ = q z' := by rw [zero_add]
    have kernelClass : H ≤ W ∨ H = ⊤ := by
      by_cases hHW : H ≤ W
      · exact Or.inl hHW
      · right
        obtain ⟨x, hxH, hxW⟩ := SetLike.not_le_iff_exists.mp hHW
        have hxControl : x.2 ≠ 0 := by
          intro hx
          apply hxW
          refine ⟨x.1, ?_⟩
          exact Prod.ext rfl hx.symm
        have dataBasisMem (i : Fin d) : (Pi.single i 1, 0) ∈ H := by
          obtain ⟨F, hF⟩ := hq (controlRewrite i) (Or.inr (Or.inr ⟨i, rfl⟩))
          have hrewrite : q (controlRewrite i x) = q (controlRewrite i 0) := by
            calc
              q (controlRewrite i x) = F (q x) := by
                simpa only [Function.comp_apply] using congrFun hF x
              _ = F (q 0) := congrArg F (show q x = q 0 from hxH)
              _ = q (controlRewrite i 0) := by
                simpa only [Function.comp_apply] using (congrFun hF 0).symm
          have hscaled : (Pi.single i x.2, 0) ∈ H := by
            have hmem := (cosetKernel _ _).mp hrewrite
            have heq : controlRewrite i x - controlRewrite i 0 =
                ((Pi.single i x.2, 0) : V) := by
              ext j <;> simp [controlRewrite]
            rwa [heq] at hmem
          have hscale :
              (x.2)⁻¹ • ((Pi.single i x.2, 0) : V) =
                ((Pi.single i 1, 0) : V) := by
            apply Prod.ext
            · funext j
              simp [Pi.single_apply, hxControl]
            · simp
          rw [← hscale]
          exact H.smul_mem _ hscaled
        let dataInclusion : (Fin d → ZMod 2) →ₗ[ZMod 2] V :=
          LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)
        let dataKernel : Submodule (ZMod 2) (Fin d → ZMod 2) :=
          H.comap dataInclusion
        have dataKernelTop : dataKernel = ⊤ :=
          (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun (ZMod 2) (Fin d))).2 (by
            intro i
            change dataInclusion ((Pi.basisFun (ZMod 2) (Fin d)) i) ∈ H
            dsimp [dataInclusion]
            rw [Pi.basisFun_apply]
            change (Pi.single i 1, 0) ∈ H
            exact dataBasisMem i)
        have hxData : (x.1, 0) ∈ H := by
          change x.1 ∈ dataKernel
          rw [dataKernelTop]
          exact Submodule.mem_top
        have hxControlPart : (0, x.2) ∈ H := by
          have hmem := H.sub_mem hxH hxData
          have heq : x - (x.1, 0) = ((0, x.2) : V) := by
            apply Prod.ext
            · funext i
              change x.1 i - x.1 i = 0
              simp
            · change x.2 - 0 = x.2
              simp
          rwa [heq] at hmem
        have controlBasisMem : (0, 1) ∈ H := by
          have hscale : (x.2)⁻¹ • ((0, x.2) : V) = ((0, 1) : V) := by
            apply Prod.ext <;> simp [hxControl]
          rw [← hscale]
          exact H.smul_mem _ hxControlPart
        exact (Submodule.eq_top_iff_forall_basis_mem stateBasis).2 (by
          intro j
          rcases j with i | j
          · rw [stateBasisData i]
            exact dataBasisMem i
          · have hj : j = () := Subsingleton.elim _ _
            subst j
            rw [stateBasisControl]
            exact controlBasisMem)
    exact ⟨H, cosetKernel, kernelClass⟩
  have ambientFinrank : Module.finrank (ZMod 2) V = d + 1 := by
    rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_self, Fintype.card_fin]
  have rangeCard : ∀ {γ : Type} (q : V → γ)
      (H : Submodule (ZMod 2) V),
      (∀ z z', q z = q z' ↔ z - z' ∈ H) →
      (Set.range q).ncard = 2 ^ (d + 1 - Module.finrank (ZMod 2) H) := by
    intro γ q H hcoset
    let quotientEquiv : Quotient (Setoid.ker q) ≃ (V ⧸ H) :=
      Quotient.congr (Equiv.refl V) (fun x y ↦
        (hcoset x y).trans H.quotientRel_def.symm)
    calc
      (Set.range q).ncard = Nat.card (Set.range q) :=
        (Nat.card_coe_set_eq (Set.range q)).symm
      _ = Nat.card (Quotient (Setoid.ker q)) :=
        (Nat.card_congr (Setoid.quotientKerEquivRange q)).symm
      _ = Nat.card (V ⧸ H) := Nat.card_congr quotientEquiv
      _ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (V ⧸ H) :=
        Module.natCard_eq_pow_finrank
      _ = 2 ^ Module.finrank (ZMod 2) (V ⧸ H) := by
        rw [Nat.card_eq_fintype_card, ZMod.card]
      _ = 2 ^ (d + 1 - Module.finrank (ZMod 2) H) := by
        rw [H.finrank_quotient, ambientFinrank]
  have quotientRealization : ∀ H : Submodule (ZMod 2) V, (H ≤ W ∨ H = ⊤) →
      DynamicallyClosed H.mkQ ∧
        ∀ z z', H.mkQ z = H.mkQ z' ↔ z - z' ∈ H := by
    intro H hH
    constructor
    · intro f hf
      rcases hf with ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩
      · refine ⟨fun q ↦ q + H.mkQ ((Pi.single i 1, 0) : V), ?_⟩
        funext z
        exact H.mkQ.map_add z ((Pi.single i 1, 0) : V)
      · refine ⟨fun q ↦ q + H.mkQ ((0, 1) : V), ?_⟩
        funext z
        exact H.mkQ.map_add z ((0, 1) : V)
      · let N : V →ₗ[ZMod 2] V :=
          (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)).comp
            ((LinearMap.single (ZMod 2) (fun _ : Fin d ↦ ZMod 2) i).comp
              (LinearMap.snd (ZMod 2) (Fin d → ZMod 2) (ZMod 2)))
        have Npreserves : H ≤ H.comap N := by
          intro x hx
          change N x ∈ H
          rcases hH with hHW | rfl
          · have hxW := hHW hx
            have hxControl : x.2 = 0 := by
              change x ∈ LinearMap.range
                (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2)) at hxW
              rw [LinearMap.range_inl] at hxW
              exact hxW
            dsimp [N]
            rw [LinearMap.snd_apply, hxControl, Pi.single_zero]
            exact H.zero_mem
          · exact Submodule.mem_top
        refine ⟨H.mapQ H N Npreserves, ?_⟩
        funext z
        change H.mkQ (N z) = H.mapQ H N Npreserves (H.mkQ z)
        exact (LinearMap.congr_fun
          (Submodule.mapQ_mkQ H H N (h := Npreserves)) z).symm
    · intro z z'
      simpa only [Submodule.mkQ_apply] using
        (Submodule.Quotient.eq H :
          (Submodule.Quotient.mk z : V ⧸ H) = Submodule.Quotient.mk z' ↔ z - z' ∈ H)
  obtain ⟨Hu, huCoset, huClass⟩ := kernelData u hu
  refine ⟨⟨Hu, huCoset, huClass⟩, ?_, ?_, ?_⟩
  · simpa only [W] using quotientRealization
  · rintro ⟨hnu, hnv⟩
    obtain ⟨Hv, hvCoset, hvClass⟩ := kernelData v hv
    have infKernel : Hu ⊓ Hv = ⊥ := by
      apply le_antisymm
      · intro z hz
        have hu0 : u z = u 0 := (huCoset z 0).2 (by simpa using hz.1)
        have hv0 : v z = v 0 := (hvCoset z 0).2 (by simpa using hz.2)
        exact (show z = 0 from hjoint (Prod.ext hu0 hv0))
      · exact bot_le
    have nontrivialKernel : ∀ {γ : Type} (q : V → γ)
        (H : Submodule (ZMod 2) V),
        (∀ z z', q z = q z' ↔ z - z' ∈ H) →
        ¬Injective q → H ≠ ⊥ := by
      intro γ q H hcoset hn hbot
      apply hn
      intro x y hxy
      have hmem := (hcoset x y).1 hxy
      rw [hbot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    have huNontrivial : Hu ≠ ⊥ := nontrivialKernel u Hu huCoset hnu
    have hvNontrivial : Hv ≠ ⊥ := nontrivialKernel v Hv hvCoset hnv
    have huW : Hu ≤ W := huClass.resolve_right (fun htop ↦ by
      apply hvNontrivial
      simpa [htop] using infKernel)
    have hvW : Hv ≤ W := hvClass.resolve_right (fun htop ↦ by
      apply huNontrivial
      simpa [htop] using infKernel)
    have WFinrank : Module.finrank (ZMod 2) W = d := by
      change Module.finrank (ZMod 2)
        (LinearMap.range (LinearMap.inl (ZMod 2) (Fin d → ZMod 2) (ZMod 2))) = d
      rw [LinearMap.finrank_range_of_inj
        (LinearMap.inl_injective (R := ZMod 2) (M := Fin d → ZMod 2)
          (M₂ := ZMod 2)), Module.finrank_pi, Fintype.card_fin]
    have dimensionIdentity :
        Module.finrank (ZMod 2) ↥(Hu ⊔ Hv) =
          Module.finrank (ZMod 2) Hu + Module.finrank (ZMod 2) Hv := by
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq Hu Hv
      rw [infKernel, finrank_bot, add_zero] at hdim
      exact hdim
    have dimensionBound :
        Module.finrank (ZMod 2) Hu + Module.finrank (ZMod 2) Hv ≤ d := by
      calc
        Module.finrank (ZMod 2) Hu + Module.finrank (ZMod 2) Hv =
            Module.finrank (ZMod 2) ↥(Hu ⊔ Hv) := dimensionIdentity.symm
        _ ≤ Module.finrank (ZMod 2) W :=
          Submodule.finrank_mono (sup_le huW hvW)
        _ = d := WFinrank
    rw [rangeCard u Hu huCoset, rangeCard v Hv hvCoset]
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · intro h hpos hupper
    let hle : h ≤ d := by omega
    let suffix := suffixCode hle
    let prefixLocal := prefixCode hle
    have suffixClosed : DynamicallyClosed suffix := by
      intro f hf
      rcases hf with ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩
      · refine ⟨fun out ↦
            ((fun j ↦ out.1 j +
              (Pi.single i (1 : ZMod 2) : Fin d → ZMod 2) ⟨h + j, by omega⟩),
              out.2), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [suffix, suffixCode]
        · simp [suffix, suffixCode]
      · refine ⟨fun out ↦ (out.1, out.2 + 1), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [suffix, suffixCode]
        · simp [suffix, suffixCode]
      · refine ⟨fun out ↦
            ((fun j ↦ (Pi.single i out.2 : Fin d → ZMod 2) ⟨h + j, by omega⟩),
              0), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [suffix, suffixCode, controlRewrite]
        · simp [suffix, suffixCode, controlRewrite]
    have prefixClosed : DynamicallyClosed prefixLocal := by
      intro f hf
      rcases hf with ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩
      · refine ⟨fun out ↦
            ((fun j ↦ out.1 j +
              (Pi.single i (1 : ZMod 2) : Fin d → ZMod 2) (Fin.castLE hle j)),
              out.2), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [prefixLocal, prefixCode]
        · simp [prefixLocal, prefixCode]
      · refine ⟨fun out ↦ (out.1, out.2 + 1), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [prefixLocal, prefixCode]
        · simp [prefixLocal, prefixCode]
      · refine ⟨fun out ↦
            ((fun j ↦
              (Pi.single i out.2 : Fin d → ZMod 2) (Fin.castLE hle j)), 0), ?_⟩
        funext z
        apply Prod.ext
        · funext j
          simp [prefixLocal, prefixCode, controlRewrite]
        · simp [prefixLocal, prefixCode, controlRewrite]
    have codesInjective : Injective (fun z ↦ (suffix z, prefixLocal z)) := by
      intro x y hxy
      have hsuffix : suffix x = suffix y := congrArg Prod.fst hxy
      have hprefix : prefixLocal x = prefixLocal y := congrArg Prod.snd hxy
      apply Prod.ext
      · funext i
        by_cases hi : i.val < h
        · let j : Fin h := ⟨i.val, hi⟩
          have hj := congrFun (congrArg Prod.fst hprefix) j
          simpa [prefixLocal, prefixCode, j] using hj
        · have hhi : h ≤ i.val := Nat.le_of_not_gt hi
          let j : Fin (d - h) := ⟨i.val - h, by omega⟩
          have hj := congrFun (congrArg Prod.fst hsuffix) j
          have hk : (⟨h + j, by omega⟩ : Fin d) = i := by
            apply Fin.ext
            simp [j]
            omega
          simpa [suffix, suffixCode, j, hk] using hj
      · exact congrArg
          (fun out : (Fin (d - h) → ZMod 2) × ZMod 2 ↦ out.2) hsuffix
    have suffixSurjective : Surjective suffix := by
      rintro ⟨q, c⟩
      let w : Fin d → ZMod 2 := fun i ↦
        if hi : h ≤ i.val then q ⟨i.val - h, by omega⟩ else 0
      refine ⟨(w, c), ?_⟩
      apply Prod.ext
      · funext i
        simp [suffix, suffixCode, w]
      · rfl
    have prefixSurjective : Surjective prefixLocal := by
      rintro ⟨p, c⟩
      let w : Fin d → ZMod 2 := fun i ↦
        if hi : i.val < h then p ⟨i.val, hi⟩ else 0
      refine ⟨(w, c), ?_⟩
      apply Prod.ext
      · funext i
        simp [prefixLocal, prefixCode, w]
      · rfl
    have suffixRange : Set.range suffix = Set.univ := Set.range_eq_univ.mpr suffixSurjective
    have prefixRange : Set.range prefixLocal = Set.univ :=
      Set.range_eq_univ.mpr prefixSurjective
    refine ⟨suffixClosed, prefixClosed, codesInjective, ?_⟩
    rw [suffixRange, prefixRange, Set.ncard_univ, Set.ncard_univ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, ZMod.card]
    rw [← pow_succ, ← pow_succ, ← pow_add]
    congr 1
    omega

#print axioms shared_control_bit_storage_bound

end D5.S3.ObserverMemory.Algorithms.SharedControlBitStorageBound
