/- GID: D5/S3/Combinatorics/PerfectMatchings/SignedBouquetBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/SignedBouquetBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derive literal untwisted and twisted one-vertex ribbon boundary counts from the restricted binary signed interlacement form. -/

import D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

namespace D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
abbrev K := ZMod 2

variable {n : ℕ} {E : Type*} [Fintype E]
abbrev D (n : ℕ) := Fin (n+1)

def jump (a : E → D n) : (D n → K) →ₗ[K] (E → K) :=
  LinearMap.pi fun e => (LinearMap.proj (cyclicNext (a e)) : (D n → K) →ₗ[K] K) - LinearMap.proj (a e)

omit [Fintype E] in
@[simp] theorem jump_apply (a : E → D n) (f : D n → K) (e : E) :
    jump a f e = f (cyclicNext (a e)) - f (a e) := rfl

noncomputable def twistDiagonal (t : E → Bool) : (E → K) →ₗ[K] (E → K) :=
  LinearMap.pi fun e => if t e then LinearMap.proj e else 0

omit [Fintype E] in
theorem twistDiagonal_apply (t : E → Bool) (z : E → K) (e : E) :
    twistDiagonal t z e = if t e then z e else 0 := by
  unfold twistDiagonal
  split <;> simp_all

noncomputable def signedDebt (a b : E → D n) (t : E → Bool) : (E → K) →ₗ[K] (E → K) :=
  endpointDebt (pairedLift a b) (pairedRead a b) + twistDiagonal t

private theorem signedDebt_is_interlace_plus_diagonal (a b : E → D n) (t : E → Bool)
    (hord : ∀ e, (a e).val < (b e).val) :
    signedDebt a b t = interlacementMap a b + twistDiagonal t := by
  unfold signedDebt
  congr 1
  ext z e
  rw [endpoint_debt_is_interlacement a b hord, interlacementMap_apply]

/-- Each original port has an incoming and outgoing gap value.
Untouched ports keep their two gaps equal. Ordinary pairings cross the
two gaps; twisted pairings match like-facing gaps. -/
def Compatible (a b : E → D n) (t : E → Bool) (f : D n → K) : Prop :=
  (∀ i, (∀ e, a e ≠ i) → (∀ e, b e ≠ i) → f (cyclicNext i) = f i) ∧
  (∀ e, if t e then
      f (a e) = f (b e) ∧ f (cyclicNext (a e)) = f (cyclicNext (b e))
    else
      f (cyclicNext (a e)) = f (b e) ∧ f (cyclicNext (b e)) = f (a e))

private theorem signedLift_at_left (a b : E → D n) (ha : Function.Injective a)
    (hd : ∀ e j, a e ≠ b j) (z : E → K) (e : E) :
    pairedLift a b z (a e) = z e := by
  classical
  rw [pairedLift_apply]
  simp [ha.eq_iff, fun j => (hd e j).symm]

private theorem signedLift_at_right (a b : E → D n) (hb : Function.Injective b)
    (hd : ∀ e j, a e ≠ b j) (z : E → K) (e : E) :
    pairedLift a b z (b e) = z e := by
  classical
  rw [pairedLift_apply]
  simp [hb.eq_iff, fun j => hd j e, ZMod.neg_eq_self_mod_two]

private theorem signedLift_at_other (a b : E → D n) (z : E → K) (i : D n)
    (ha : ∀ e, a e ≠ i) (hb : ∀ e, b e ≠ i) :
    pairedLift a b z i = 0 := by
  classical
  simp [pairedLift_apply, ha, hb]

/-- Extracting one jump per band eliminates the four local flag values.
A twist changes only the diagonal debt, not the cyclic jump equation. -/
private theorem compatible_iff_signed_equations (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ e j, a e ≠ b j)
    (f : D n → K) :
    Compatible a b t f ↔
      (∀ i, f (cyclicNext i)-f i = pairedLift a b (jump a f) i) ∧
      ∀ e, pairedRead a b f e = if t e then 0 else jump a f e := by
  constructor
  · rintro ⟨hfix, hpair⟩
    refine ⟨fun i => ?_, fun e => ?_⟩
    · by_cases hA : ∃ e, a e = i
      · obtain ⟨e,rfl⟩ := hA
        rw [signedLift_at_left _ _ ha hd, jump_apply]
      by_cases hB : ∃ e, b e = i
      · obtain ⟨e,rfl⟩ := hB
        rw [signedLift_at_right _ _ hb hd, jump_apply]
        have h := hpair e
        cases ht : t e
        · simp [ht] at h
          rw [h.1,h.2, ← neg_sub, ZMod.neg_eq_self_mod_two]
        · simp [ht] at h
          rw [h.1,h.2]
      push Not at hA hB
      rw [signedLift_at_other _ _ _ _ hA hB,hfix _ hA hB,sub_self]
    · have h := hpair e
      cases ht : t e <;> simp [ht] at h ⊢
      · rw [h.1]
      · rw [h.1,sub_self]
  · rintro ⟨hder,hread⟩
    refine ⟨fun i ai bi => ?_, fun e => ?_⟩
    · exact sub_eq_zero.mp ((hder i).trans (signedLift_at_other _ _ _ _ ai bi))
    · have hB := (hder (b e)).trans (signedLift_at_right _ _ hb hd _ _)
      rw [jump_apply] at hB
      have hr := hread e
      cases ht : t e
      · simp [ht] at hr ⊢
        refine ⟨?_, ?_⟩
        · exact hr.symm
        · have he := ZMod.neg_eq_self_mod_two (f (a e) - f (b e))
          rw [neg_sub] at he
          exact sub_left_inj.mp (hB.trans (by simpa only [← hr] using he))
      · simp [ht] at hr ⊢
        have heq := sub_eq_zero.mp hr
        rw [heq] at hB
        exact ⟨heq.symm, (sub_left_inj.mp hB).symm⟩

end D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
#print axioms D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.signedDebt_is_interlace_plus_diagonal
#print axioms D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.compatible_iff_signed_equations

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

namespace D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
variable {n : ℕ} {E : Type*} [Fintype E]

private def deriv (n : ℕ) : (D n → K) →ₗ[K] (D n → K) :=
  LinearMap.pi fun i => (LinearMap.proj (cyclicNext i) : (D n → K) →ₗ[K] K) - LinearMap.proj i

@[simp] private theorem deriv_apply (f : D n → K) (i : D n) :
    deriv n f i = f (cyclicNext i) - f i := rfl

noncomputable def signedConstant (a b : E → D n) (t : E → Bool) :
    Submodule K (D n → K) :=
  (deriv n - (pairedLift a b).comp (jump a)).ker ⊓
    (pairedRead a b - (LinearMap.id - twistDiagonal t).comp (jump a)).ker

private theorem mem_signedConstant_iff (a b : E → D n) (t : E → Bool) (f : D n → K) :
    f ∈ signedConstant a b t ↔
      (∀ i, f (cyclicNext i) - f i = pairedLift a b (jump a f) i) ∧
      ∀ e, pairedRead a b f e = if t e then 0 else jump a f e := by
  simp only [signedConstant, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero]
  constructor
  · rintro ⟨h₁,h₂⟩
    refine ⟨fun i => congrFun h₁ i, fun e => ?_⟩
    have h := congrFun h₂ e
    cases ht : t e <;> simpa [twistDiagonal_apply, ht] using h
  · rintro ⟨h₁,h₂⟩
    refine ⟨funext h₁, funext fun e => ?_⟩
    have h := h₂ e
    cases ht : t e <;> simpa [twistDiagonal_apply, ht] using h

private theorem debt_zero_iff (a b : E → D n) (t : E → Bool) (z : E → K) :
    z ∈ (signedDebt a b t).ker ↔ ∀ e,
      pairedRead a b (prefixLinear n (pairedLift a b z)) e = if t e then 0 else z e := by
  simp only [LinearMap.mem_ker]
  have elem (e : E) : signedDebt a b t z e = 0 ↔
      pairedRead a b (prefixLinear n (pairedLift a b z)) e = if t e then 0 else z e := by
    simp only [signedDebt, endpointDebt, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, twistDiagonal_apply]
    cases ht : t e
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, sub_eq_zero]
    · simp only [↓reduceIte, sub_add_cancel]
  exact ⟨fun h e => (elem e).1 (congrFun h e), fun h => funext fun e => (elem e).2 (h e)⟩

/-- Exact inverse: integrate the band jumps to recover every gap value.
Twists change the linear compatibility matrix but no reconstruction data. -/
noncomputable def signedConstantEquiv (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hd : ∀ e j, a e ≠ b j) :
    signedConstant a b t ≃ₗ[K] K × (signedDebt a b t).ker where
  toFun x := ⟨x.val 0, ⟨jump a x.val, by
    obtain ⟨hstep,hread⟩ := (mem_signedConstant_iff a b t x.val).1 x.prop
    apply (debt_zero_iff a b t _).2
    have he : x.val = fun i => x.val 0 + prefixLinear n (pairedLift a b (jump a x.val)) i :=
      funext (cyclic_prefix_recovers x.val _ hstep)
    have hread' := congrArg (pairedRead a b) he
    rw [pairedRead_shift] at hread'
    intro e
    rw [← hread']
    exact hread e⟩⟩
  invFun y := ⟨fun i => y.1 + prefixLinear n (pairedLift a b y.2.val) i, by
    apply (mem_signedConstant_iff a b t _).2
    have hstep := cyclic_prefix_primitive (pairedLift a b y.2.val) (paired_sum_zero a b y.2.val) y.1
    have hrec : jump a (fun i => y.1 + prefixLinear n (pairedLift a b y.2.val) i) = y.2.val := by
      funext e
      rw [jump_apply]
      exact (hstep (a e)).trans (signedLift_at_left _ _ ha hd _ _)
    rw [hrec, pairedRead_shift]
    exact ⟨hstep,(debt_zero_iff a b t _).1 y.2.prop⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (cyclic_prefix_recovers x.val _ ((mem_signedConstant_iff a b t x.val).1 x.prop).1 i).symm
  right_inv y := by
    apply Prod.ext
    · change y.1+cyclicPrefix (pairedLift a b y.2.val) 0=y.1
      simp [cyclicPrefix]
    · apply Subtype.ext
      funext e
      exact (cyclic_prefix_primitive _ (paired_sum_zero a b y.2.val) y.1 (a e)).trans
        (signedLift_at_left _ _ ha hd _ _)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_add (jump a) x.val y.val)
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (map_smul (jump a) c x.val)

private theorem signed_dim_plus_rank (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hd : ∀ e j, a e ≠ b j)
    (hord : ∀ e, (a e).val < (b e).val) :
    Module.finrank K (signedConstant a b t) +
      Module.finrank K (interlacementMap a b + twistDiagonal t).range =
      1 + Fintype.card E := by
  have he := (signedConstantEquiv a b t ha hd).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at he
  have hr := LinearMap.finrank_range_add_finrank_ker (signedDebt a b t)
  rw [Module.finrank_fintype_fun_eq_card] at hr
  rw [← signedDebt_is_interlace_plus_diagonal a b t hord]
  rw [he, add_assoc, Nat.add_comm (Module.finrank K (signedDebt a b t).ker), hr]

end D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
#print axioms D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.signed_dim_plus_rank

open Relation
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank

namespace D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
variable {n : ℕ} {E : Type*} [Fintype E]
abbrev Flag (n : ℕ) := D n × Bool

def inFlag (i : D n) : Flag n := (i,false)
def outFlag (i : D n) : Flag n := (i,true)

omit [Fintype E] in
/-- Original flags, with arcs along the vertex and one true matching on
each selected band. Untouched endpoints are capped. -/
inductive FlagLink (a b : E → D n) (t : E → Bool) : Flag n → Flag n → Prop
  | arc (i) : FlagLink a b t (outFlag i) (inFlag (cyclicNext i))
  | cap (i) (ha : ∀ e, a e ≠ i) (hb : ∀ e, b e ≠ i) :
      FlagLink a b t (outFlag i) (inFlag i)
  | crossA (e) (ht : t e = false) : FlagLink a b t (outFlag (a e)) (inFlag (b e))
  | crossB (e) (ht : t e = false) : FlagLink a b t (outFlag (b e)) (inFlag (a e))
  | twistIn (e) (ht : t e = true) : FlagLink a b t (inFlag (a e)) (inFlag (b e))
  | twistOut (e) (ht : t e = true) : FlagLink a b t (outFlag (a e)) (outFlag (b e))

omit [Fintype E] in
def boundarySetoid (a b : E → D n) (t : E → Bool) : Setoid (Flag n) where
  r := EqvGen (FlagLink a b t)
  iseqv := ⟨.refl, fun h => .symm _ _ h, fun h₁ h₂ => .trans _ _ _ h₁ h₂⟩

def gap (s : Flag n) : D n := if s.2 then cyclicNext s.1 else s.1

@[simp] theorem gap_in (i : D n) : gap (inFlag i) = i := rfl
@[simp] theorem gap_out (i : D n) : gap (outFlag i) = cyclicNext i := rfl

omit [Fintype E] in
private theorem compatible_link (a b : E → D n) (t : E → Bool) (f : D n → K)
    (h : Compatible a b t f) {s u} (l : FlagLink a b t s u) : f (gap s) = f (gap u) := by
  cases l with
  | arc i => rfl
  | cap i ha hb => exact h.1 i ha hb
  | crossA e ht => exact (by simpa [ht] using h.2 e : _ ∧ _).1
  | crossB e ht => exact (by simpa [ht] using h.2 e : _ ∧ _).2
  | twistIn e ht => exact (by simpa [ht] using h.2 e : _ ∧ _).1
  | twistOut e ht => exact (by simpa [ht] using h.2 e : _ ∧ _).2

omit [Fintype E] in
private theorem compatible_boundary (a b : E → D n) (t : E → Bool) (f : D n → K)
    (h : Compatible a b t f) {s u} (l : (boundarySetoid a b t).r s u) :
    f (gap s) = f (gap u) := by
  induction l with
  | rel _ _ hl => exact compatible_link _ _ _ _ h hl
  | refl _ => rfl
  | symm _ _ _ hl => exact hl.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

omit [Fintype E] in
private theorem mk_link (a b : E → D n) (t : E → Bool) {s u}
    (l : FlagLink a b t s u) :
    (Quotient.mk (boundarySetoid a b t) s) = Quotient.mk _ u :=
  Quotient.sound (.rel _ _ l)

private theorem mk_gap (a b : E → D n) (t : E → Bool) (s : Flag n) :
    (Quotient.mk (boundarySetoid a b t) (inFlag (gap s))) = Quotient.mk _ s := by
  obtain ⟨i,k⟩ := s
  cases k
  · rfl
  · exact (mk_link _ _ _ (.arc i)).symm

private theorem pull_compatible (a b : E → D n) (t : E → Bool)
    (v : Quotient (boundarySetoid a b t) → K) :
    Compatible a b t (fun i => v (Quotient.mk _ (inFlag i))) := by
  have hu (s : Flag n) := congrArg v (mk_gap a b t s)
  have hl {s u} (l : FlagLink a b t s u) :
      v (Quotient.mk _ (inFlag (gap s))) = v (Quotient.mk _ (inFlag (gap u))) :=
    (hu s).trans ((congrArg v (mk_link _ _ _ l)).trans (hu u).symm)
  refine ⟨fun i ha hb => hl (.cap i ha hb), fun e => ?_⟩
  cases ht : t e
  · simpa [ht] using And.intro (hl (.crossA e ht)) (hl (.crossB e ht))
  · simpa [ht] using And.intro (hl (.twistIn e ht)) (hl (.twistOut e ht))

/-- No independently supplied boundary classifier. All functions on the
actual flag circles are exactly the compatible binary gap assignments. -/
noncomputable def signedFlagBoundaryEquiv (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ e j, a e ≠ b j) :
    signedConstant a b t ≃ₗ[K] (Quotient (boundarySetoid a b t) → K) where
  toFun x := Quotient.lift (fun s => x.val (gap s)) (fun _ _ hr =>
    compatible_boundary _ _ _ _ ((compatible_iff_signed_equations _ _ _ ha hb hd _).2
      ((mem_signedConstant_iff _ _ _ _).1 x.prop)) hr)
  invFun v := ⟨fun i => v (Quotient.mk _ (inFlag i)),
    (mem_signedConstant_iff _ _ _ _).2 ((compatible_iff_signed_equations _ _ _ ha hb hd _).1
      (pull_compatible _ _ _ v))⟩
  left_inv _ := rfl
  right_inv v := by
    funext q
    obtain ⟨s,rfl⟩ := Quotient.exists_rep q
    exact congrArg v (mk_gap _ _ _ s)
  map_add' x y := by
    funext q
    obtain ⟨s,rfl⟩ := Quotient.exists_rep q
    rfl
  map_smul' c x := by
    funext q
    obtain ⟨s,rfl⟩ := Quotient.exists_rep q
    rfl

/-- Signed Cohn–Lempel equality on the actual four-flag topology.
The diagonal twist bit is exact, including its contribution at odd Euler genus. -/
theorem signed_flag_boundary_plus_rank (a b : E → D n) (t : E → Bool)
    (ha : Function.Injective a) (hb : Function.Injective b) (hd : ∀ e j, a e ≠ b j)
    (hord : ∀ e, (a e).val < (b e).val) :
    Nat.card (Quotient (boundarySetoid a b t)) +
      Module.finrank K (interlacementMap a b + twistDiagonal t).range =
      1 + Fintype.card E := by
  classical
  let _ := Fintype.ofFinite (Quotient (boundarySetoid a b t))
  have he := (signedFlagBoundaryEquiv a b t ha hb hd).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at he
  rw [← he]
  exact signed_dim_plus_rank a b t ha hd hord

end D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
#print axioms D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary.signed_flag_boundary_plus_rank

namespace D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
open D5.S3.Combinatorics.PerfectMatchings.RibbonCohomologyRank
variable {n : ℕ} {E : Type*}
noncomputable def signedBouquetCircleCount (a b : E → D n) (t : E → Bool) (S : Finset E) : ℕ :=
  Nat.card (Quotient (boundarySetoid (fun i : S => a i) (fun i : S => b i) (fun i : S => t i)))
end D5.S3.Combinatorics.PerfectMatchings.SignedBouquetBoundary
