/- GID: D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Factors]
   utility: none
   digest: Actual finite cut modules compose in series on their original carriers. -/
import D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch

/-! Actual serial composition of finite four-port alternating systems. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
noncomputable section
open Equiv FiniteEndpointPairing FiniteBandSwitch FourEndpoint
universe u

/-- A finite actual corner/band system with exactly four labelled exposed flags. -/
structure CutModule where
  Carrier : Type u
  finite : Finite Carrier
  corner : Perm Carrier
  band : Perm Carrier
  corner_involutive : Function.Involutive corner
  band_involutive : Function.Involutive band
  corner_free : ∀ x, corner x ≠ x
  ports : Fin 4 ≃ {x // band x = x}

attribute [instance] CutModule.finite

namespace CutModule

def pairing (M : CutModule.{u}) : Perm (Fin 4) :=
  M.ports.symm.permCongr
    (endpointPairing M.corner M.band M.corner_involutive M.band_involutive)

private theorem pairing_involutive (M : CutModule.{u}) :
    Function.Involutive M.pairing := by
  intro i
  simpa only [pairing, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
    congrArg M.ports.symm
      (endpoint_pairing_involutive M.corner M.band M.corner_involutive
        M.band_involutive (M.ports i))

private theorem pairing_free (M : CutModule.{u}) : ∀ i, M.pairing i ≠ i := by
  intro i hi
  apply endpoint_pairing_fixed_point_free M.corner M.band M.corner_involutive
    M.band_involutive M.corner_free (M.ports i)
  simpa only [pairing, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply] using congrArg M.ports hi

private theorem cycle_iff (M : CutModule.{u}) (i j : Fin 4) :
    (M.corner * M.band).SameCycle (M.ports i) (M.ports j) ↔
      M.pairing.SameCycle i j := by
  classical
  have h := endpoint_pairing_reattach_same_cycle M.corner M.band
    M.corner_involutive M.band_involutive 1 (M.ports i) (M.ports j)
  have hc := same_cycle_perm_congr M.ports.symm
    (endpointPairing M.corner M.band M.corner_involutive M.band_involutive)
    (M.ports i) (M.ports j)
  simpa only [map_one, mul_one, Equiv.symm_apply_apply, pairing] using
    h.trans hc.symm

private theorem through_iff (M : CutModule.{u}) :
    M.pairing ≠ thirdPairing ↔
      ¬ (M.corner * M.band).SameCycle (M.ports 0) (M.ports 1) := by
  rw [M.cycle_iff, same_cycle_involutive_iff M.pairing M.pairing_involutive]
  rcases pairing_three_forms M.pairing M.pairing_involutive M.pairing_free with h | h | h
  all_goals rw [h]; decide

end CutModule

theorem two_forms (c : Perm (Fin 2)) : c = 1 ∨ c = swap 0 1 := by
  generalize h0 : c (0 : Fin 2) = z
  fin_cases z
  · have h1 : c 1 = 1 := by
      generalize hv : c (1 : Fin 2) = v
      fin_cases v
      · exact False.elim (by have := c.injective (hv.trans h0.symm); omega)
      · rfl
    left
    ext i
    fin_cases i <;> simp [h0, h1]
  · have h1 : c 1 = 0 := by
      generalize hv : c (1 : Fin 2) = v
      fin_cases v
      · rfl
      · exact False.elim (by have := c.injective (hv.trans h0.symm); omega)
    right
    ext i
    fin_cases i <;> simp [h0, h1]

/-- Join the right pair of the first module to the left pair of the second. -/
def connector (c : Perm (Fin 2)) : Perm (Fin 4 ⊕ Fin 4) :=
  swap (Sum.inl 2) (Sum.inr ((c 0).castAdd 2)) *
    swap (Sum.inl 3) (Sum.inr ((c 1).castAdd 2))

/-- The two left flags of the first module and two right flags of the second. -/
def outerIndex : Fin 4 → Fin 4 ⊕ Fin 4 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inr 2, Sum.inr 3]

private theorem outer_index_injective : Function.Injective outerIndex := by decide

private theorem connector_involutive (c : Perm (Fin 2)) :
    Function.Involutive (connector c) := by
  rcases two_forms c with rfl | rfl
  all_goals intro z; rcases z with i | i <;> fin_cases i <;> rfl

private theorem connector_fixed (c : Perm (Fin 2)) (z : Fin 4 ⊕ Fin 4) :
    connector c z = z ↔ ∃ i, outerIndex i = z := by
  rcases two_forms c with rfl | rfl
  all_goals rcases z with i | i <;> fin_cases i <;> decide

private theorem connector_outer (c : Perm (Fin 2)) (i : Fin 4) :
    connector c (outerIndex i) = outerIndex i :=
  (connector_fixed c _).mpr ⟨i, rfl⟩

namespace CutModule
attribute [local instance] Classical.propDecidable
variable (M N : CutModule.{u})

private def sumCorner : Perm (M.Carrier ⊕ N.Carrier) :=
  Perm.sumCongr M.corner N.corner

private def sumBand : Perm (M.Carrier ⊕ N.Carrier) :=
  Perm.sumCongr M.band N.band

private theorem sum_corner_involutive : Function.Involutive (sumCorner M N) := by
  rintro (x | y)
  · exact congrArg Sum.inl (M.corner_involutive x)
  · exact congrArg Sum.inr (N.corner_involutive y)

private theorem sum_band_involutive : Function.Involutive (sumBand M N) := by
  rintro (x | y)
  · exact congrArg Sum.inl (M.band_involutive x)
  · exact congrArg Sum.inr (N.band_involutive y)

private theorem sum_corner_free : ∀ x, sumCorner M N x ≠ x := by
  rintro (x | y) h
  · exact M.corner_free x (Sum.inl.inj h)
  · exact N.corner_free y (Sum.inr.inj h)

private def sumPorts : (Fin 4 ⊕ Fin 4) ≃ {x // sumBand M N x = x} where
  toFun
    | Sum.inl i => ⟨Sum.inl (M.ports i), congrArg Sum.inl (M.ports i).property⟩
    | Sum.inr j => ⟨Sum.inr (N.ports j), congrArg Sum.inr (N.ports j).property⟩
  invFun x := match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl (M.ports.symm ⟨a, Sum.inl.inj h⟩)
    | ⟨Sum.inr b, h⟩ => Sum.inr (N.ports.symm ⟨b, Sum.inr.inj h⟩)
  left_inv := by
    rintro (i | j) <;> simp
  right_inv := by
    rintro ⟨x | y, h⟩ <;> apply Subtype.ext <;> simp

private def joinedBand (c : Perm (Fin 2)) : Perm (M.Carrier ⊕ N.Carrier) :=
  closeBoundary (sumBand M N) ((sumPorts M N).permCongr (connector c))

private theorem joined_band_at (c : Perm (Fin 2)) (z : Fin 4 ⊕ Fin 4) :
    joinedBand M N c (sumPorts M N z) = (sumPorts M N (connector c z) : M.Carrier ⊕ N.Carrier) := by
  classical
  simp only [joinedBand, closeBoundary, Perm.mul_apply, Perm.ofSubtype_apply_coe,
    Equiv.permCongr_apply, Equiv.symm_apply_apply, (sumPorts M N _).property]

private theorem joined_band_off (c : Perm (Fin 2)) (x : M.Carrier ⊕ N.Carrier)
    (hx : sumBand M N x ≠ x) : joinedBand M N c x = sumBand M N x := by
  classical
  unfold joinedBand closeBoundary
  rw [Perm.mul_apply]
  congr 1
  exact @Perm.ofSubtype_apply_of_not_mem _ _
    (fun _ => Classical.propDecidable _) x _ hx

private theorem joined_band_involutive (c : Perm (Fin 2)) :
    Function.Involutive (joinedBand M N c) := by
  intro x
  by_cases hx : sumBand M N x = x
  · obtain ⟨z, hz⟩ := (sumPorts M N).surjective ⟨x, hx⟩
    have hzx : (sumPorts M N z : M.Carrier ⊕ N.Carrier) = x := congrArg Subtype.val hz
    rw [← hzx, joined_band_at, joined_band_at, connector_involutive c z]
  · have hnot : sumBand M N (sumBand M N x) ≠ sumBand M N x := by
      rw [sum_band_involutive]
      exact Ne.symm hx
    rw [joined_band_off M N c x hx, joined_band_off M N c _ hnot,
      sum_band_involutive]

private def joinedLabel (c : Perm (Fin 2)) (i : Fin 4) :
    {x // joinedBand M N c x = x} :=
  ⟨sumPorts M N (outerIndex i), by rw [joined_band_at, connector_outer]⟩

private theorem joined_label_bijective (c : Perm (Fin 2)) :
    Function.Bijective (joinedLabel M N c) := by
  constructor
  · intro i j h
    apply outer_index_injective
    apply (sumPorts M N).injective
    apply Subtype.ext
    exact congrArg (fun z : {x // joinedBand M N c x = x} => z.val) h
  · intro x
    have hx : sumBand M N x = x := by
      by_contra hn
      exact hn ((joined_band_off M N c x hn).symm.trans x.property)
    obtain ⟨z, hz⟩ := (sumPorts M N).surjective ⟨x, hx⟩
    have hzx : (sumPorts M N z : M.Carrier ⊕ N.Carrier) = x := congrArg Subtype.val hz
    have hj : connector c z = z := by
      apply (sumPorts M N).injective
      apply Subtype.ext
      rw [← joined_band_at, hzx, x.property]
    obtain ⟨i, hi⟩ := (connector_fixed c z).mp hj
    refine ⟨i, Subtype.ext ?_⟩
    change (sumPorts M N (outerIndex i) : M.Carrier ⊕ N.Carrier) = x
    rw [hi, hzx]

/-- The actual composite retains all original flags, including closed components. -/
def join (c : Perm (Fin 2)) : CutModule.{u} where
  Carrier := M.Carrier ⊕ N.Carrier
  finite := inferInstance
  corner := sumCorner M N
  band := joinedBand M N c
  corner_involutive := sum_corner_involutive M N
  band_involutive := joined_band_involutive M N c
  corner_free := sum_corner_free M N
  ports := Equiv.ofBijective (joinedLabel M N c) (joined_label_bijective M N c)


private theorem sum_walk_inl (n : ℕ) (x : M.Carrier) :
    ((sumCorner M N * sumBand M N) ^ n) (Sum.inl x) =
      Sum.inl (((M.corner * M.band) ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    rfl

private theorem sum_walk_inr (n : ℕ) (x : N.Carrier) :
    ((sumCorner M N * sumBand M N) ^ n) (Sum.inr x) =
      Sum.inr (((N.corner * N.band) ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply]
    rfl

private theorem sum_pairing_apply (z : Fin 4 ⊕ Fin 4) :
    endpointPairing (sumCorner M N) (sumBand M N)
        (sum_corner_involutive M N) (sum_band_involutive M N) (sumPorts M N z) =
      sumPorts M N (Perm.sumCongr M.pairing N.pairing z) := by
  classical
  rcases z with i | i
  · obtain ⟨n, hn, _, hend⟩ := endpoint_pairing_reattach_return_data
      M.corner M.band M.corner_involutive M.band_involutive 1 (M.ports i)
    simp only [Perm.one_apply, map_one, mul_one] at hn hend
    have hfirst : FirstVisit (sumCorner M N * sumBand M N)
        {x | sumBand M N x = x} (sumPorts M N (Sum.inl i)) n := by
      refine ⟨hn.1, ?_, ?_⟩
      · change sumBand M N (((sumCorner M N * sumBand M N) ^ n)
          (Sum.inl (M.ports i))) =
            ((sumCorner M N * sumBand M N) ^ n) (Sum.inl (M.ports i))
        simp only [sum_walk_inl]
        exact congrArg Sum.inl hn.2.1
      · intro k hk hkn hmem
        apply hn.2.2 k hk hkn
        change sumBand M N (((sumCorner M N * sumBand M N) ^ k)
          (Sum.inl (M.ports i))) =
            ((sumCorner M N * sumBand M N) ^ k) (Sum.inl (M.ports i)) at hmem
        simp only [sum_walk_inl] at hmem
        exact Sum.inl.inj hmem
    apply Subtype.ext
    change (nextVisit (sumCorner M N * sumBand M N)
      ({x | sumBand M N x = x} : Set (M.Carrier ⊕ N.Carrier))
      (sumPorts M N (Sum.inl i)) : M.Carrier ⊕ N.Carrier) =
      Sum.inl (M.ports (M.pairing i) : M.Carrier)
    rw [next_visit_eq_of_first_visit _ hfirst]
    change ((sumCorner M N * sumBand M N) ^ n) (Sum.inl (M.ports i)) = _
    rw [sum_walk_inl]
    simpa only [pairing, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using congrArg Sum.inl hend
  · obtain ⟨n, hn, _, hend⟩ := endpoint_pairing_reattach_return_data
      N.corner N.band N.corner_involutive N.band_involutive 1 (N.ports i)
    simp only [Perm.one_apply, map_one, mul_one] at hn hend
    have hfirst : FirstVisit (sumCorner M N * sumBand M N)
        {x | sumBand M N x = x} (sumPorts M N (Sum.inr i)) n := by
      refine ⟨hn.1, ?_, ?_⟩
      · change sumBand M N (((sumCorner M N * sumBand M N) ^ n)
          (Sum.inr (N.ports i))) =
            ((sumCorner M N * sumBand M N) ^ n) (Sum.inr (N.ports i))
        simp only [sum_walk_inr]
        exact congrArg Sum.inr hn.2.1
      · intro k hk hkn hmem
        apply hn.2.2 k hk hkn
        change sumBand M N (((sumCorner M N * sumBand M N) ^ k)
          (Sum.inr (N.ports i))) =
            ((sumCorner M N * sumBand M N) ^ k) (Sum.inr (N.ports i)) at hmem
        simp only [sum_walk_inr] at hmem
        exact Sum.inr.inj hmem
    apply Subtype.ext
    change (nextVisit (sumCorner M N * sumBand M N)
      ({x | sumBand M N x = x} : Set (M.Carrier ⊕ N.Carrier))
      (sumPorts M N (Sum.inr i)) : M.Carrier ⊕ N.Carrier) =
      Sum.inr (N.ports (N.pairing i) : N.Carrier)
    rw [next_visit_eq_of_first_visit _ hfirst]
    change ((sumCorner M N * sumBand M N) ^ n) (Sum.inr (N.ports i)) = _
    rw [sum_walk_inr]
    simpa only [pairing, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] using congrArg Sum.inr hend

private theorem sum_pairing :
    (sumPorts M N).symm.permCongr
      (endpointPairing (sumCorner M N) (sumBand M N)
        (sum_corner_involutive M N) (sum_band_involutive M N)) =
      Perm.sumCongr M.pairing N.pairing := by
  ext z
  apply (sumPorts M N).injective
  simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    using sum_pairing_apply M N z

private theorem joined_cycles (c : Perm (Fin 2)) (z w : Fin 4 ⊕ Fin 4) :
    (sumCorner M N * joinedBand M N c).SameCycle (sumPorts M N z) (sumPorts M N w) ↔
      (Perm.sumCongr M.pairing N.pairing * connector c).SameCycle z w := by
  classical
  have horbit := endpoint_pairing_reattach_same_cycle (sumCorner M N) (sumBand M N)
    (sum_corner_involutive M N) (sum_band_involutive M N)
    ((sumPorts M N).permCongr (connector c)) (sumPorts M N z) (sumPorts M N w)
  unfold joinedBand closeBoundary
  apply horbit.trans
  have hrestore : (sumPorts M N).permCongr (Perm.sumCongr M.pairing N.pairing) =
      endpointPairing (sumCorner M N) (sumBand M N)
        (sum_corner_involutive M N) (sum_band_involutive M N) := by
    rw [← sum_pairing]
    exact (sumPorts M N).permCongr.apply_symm_apply _
  rw [← hrestore, ← Equiv.permCongr_mul]
  exact same_cycle_perm_congr (sumPorts M N) _ z w

end CutModule

private theorem compressed_serial (P Q : Perm (Fin 4))
    (hP : Function.Involutive P) (hQ : Function.Involutive Q)
    (hPf : ∀ i, P i ≠ i) (hQf : ∀ i, Q i ≠ i) (c : Perm (Fin 2)) :
    ¬ (Perm.sumCongr P Q * connector c).SameCycle (Sum.inl 0) (Sum.inl 1) ↔
      P ≠ thirdPairing ∧ Q ≠ thirdPairing := by
  rcases pairing_three_forms P hP hPf with rfl | rfl | rfl <;>
    rcases pairing_three_forms Q hQ hQf with rfl | rfl | rfl <;>
      rcases two_forms c with rfl | rfl
  all_goals decide

namespace CutModule

/-- Actual binary series composition is through exactly when both factors are. -/
private theorem join_through (M N : CutModule.{u}) (c : Perm (Fin 2)) :
    (M.join N c).pairing ≠ thirdPairing ↔
      M.pairing ≠ thirdPairing ∧ N.pairing ≠ thirdPairing := by
  rw [(M.join N c).through_iff]
  change (¬ (sumCorner M N * joinedBand M N c).SameCycle
    (sumPorts M N (Sum.inl 0)) (sumPorts M N (Sum.inl 1))) ↔ _
  rw [joined_cycles]
  exact compressed_serial M.pairing N.pairing M.pairing_involutive
    N.pairing_involutive M.pairing_free N.pairing_free c

/-- Build a nonempty actual chain by attaching each final module at its two left flags. -/
def serial : (n : ℕ) → (Fin (n + 1) → CutModule.{u}) →
    (Fin n → Perm (Fin 2)) → CutModule.{u}
  | 0, M, _ => M 0
  | n + 1, M, c =>
    (serial n (fun i => M i.castSucc) (fun i => c i.castSucc)).join
      (M (Fin.last (n + 1))) (c (Fin.last n))

/-- For every nonempty length and every connector bijection, the original actual
outer endpoint pairing is through exactly when every original module is through. -/
private theorem serial_through (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) :
    (serial n M c).pairing ≠ thirdPairing ↔ ∀ i, (M i).pairing ≠ thirdPairing := by
  induction n with
  | zero => simp [serial, Fin.forall_fin_one]
  | succ n ih =>
    rw [serial, join_through, ih]
    constructor
    · rintro ⟨h, hlast⟩ i
      exact Fin.lastCases hlast (fun j => h j) i
    · intro h
      exact ⟨fun i => h i.castSucc, h (Fin.last (n + 1))⟩

end CutModule

namespace CutModule

private def splitCarrier (n : ℕ) (M : Fin (n + 2) → CutModule.{u}) :
    (Σ i, (M i).Carrier) ≃
      (Σ i : Fin (n + 1), (M i.castSucc).Carrier) ⊕ (M (Fin.last (n + 1))).Carrier where
  toFun p := Fin.lastCases (fun x => Sum.inr x)
    (fun i x => Sum.inl ⟨i, x⟩) p.1 p.2
  invFun
    | Sum.inl ⟨i, x⟩ => ⟨i.castSucc, x⟩
    | Sum.inr x => ⟨Fin.last (n + 1), x⟩
  left_inv := by
    rintro ⟨i, x⟩
    cases i using Fin.lastCases <;> simp
  right_inv := by
    rintro (⟨i, x⟩ | x) <;> simp

private def oneCarrier (M : Fin 1 → CutModule.{u}) :
    (Σ i, (M i).Carrier) ≃ (M 0).Carrier where
  toFun p := Fin.cases (fun x => x) (fun i => Fin.elim0 i) p.1 p.2
  invFun x := ⟨0, x⟩
  left_inv := by rintro ⟨i, x⟩; fin_cases i; rfl
  right_inv _ := rfl

/-- Every original flag is retained once in the recursive disjoint union. -/
def carrierEquiv : (n : ℕ) → (M : Fin (n + 1) → CutModule.{u}) →
    (c : Fin n → Perm (Fin 2)) → (Σ i, (M i).Carrier) ≃ (serial n M c).Carrier
  | 0, M, _ => oneCarrier M
  | n + 1, M, c => (splitCarrier n M).trans
    (Equiv.sumCongr
      (carrierEquiv n (fun i => M i.castSucc) (fun i => c i.castSucc))
      (Equiv.refl _))

private theorem carrier_corner (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) (i : Fin (n + 1)) (x : (M i).Carrier) :
    (serial n M c).corner (carrierEquiv n M c ⟨i, x⟩) =
      carrierEquiv n M c ⟨i, (M i).corner x⟩ := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.lastCases with
    | last => simp [carrierEquiv, splitCarrier, serial, join, sumCorner, Equiv.coe_trans, Function.comp_apply]
    | cast i =>
      simpa [carrierEquiv, splitCarrier, serial, join, sumCorner] using
        congrArg (Sum.inl : _ → _ ⊕ (M (Fin.last (n + 1))).Carrier)
          (ih (fun j => M j.castSucc) (fun j => c j.castSucc) i x)

private theorem carrier_left (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) (a : Fin 2) :
    ((serial n M c).ports (a.castAdd 2) : (serial n M c).Carrier) =
      carrierEquiv n M c ⟨0, ((M 0).ports (a.castAdd 2) : (M 0).Carrier)⟩ := by
  induction n with
  | zero => fin_cases a <;> rfl
  | succ n ih =>
    have h := congrArg (Sum.inl : _ → _ ⊕ (M (Fin.last (n + 1))).Carrier)
      (ih (fun i => M i.castSucc) (fun i => c i.castSucc))
    have ho : outerIndex (a.castAdd 2) = Sum.inl (a.castAdd 2) := by
      fin_cases a <;> rfl
    rw [← Fin.castSucc_zero (n := n + 1)]
    simpa only [carrierEquiv, splitCarrier, serial, join, joinedLabel, ho,
      sumPorts, Equiv.ofBijective, Equiv.trans_apply, Equiv.sumCongr_apply,
      Equiv.coe_fn_mk, Fin.lastCases_castSucc, Sum.map_inl, Sum.inl.injEq] using h

private theorem carrier_right (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) (a : Fin 2) :
    ((serial n M c).ports (a.natAdd 2) : (serial n M c).Carrier) =
      carrierEquiv n M c
        ⟨Fin.last n, ((M (Fin.last n)).ports (a.natAdd 2) : (M (Fin.last n)).Carrier)⟩ := by
  cases n with
  | zero => fin_cases a <;> rfl
  | succ n =>
    fin_cases a <;>
      simp [carrierEquiv, splitCarrier, serial, join, joinedLabel, outerIndex, sumPorts, Equiv.coe_trans, Function.comp_apply, Equiv.ofBijective]

private theorem carrier_band_off (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) (i : Fin (n + 1)) (x : (M i).Carrier)
    (hx : (M i).band x ≠ x) :
    (serial n M c).band (carrierEquiv n M c ⟨i, x⟩) =
      carrierEquiv n M c ⟨i, (M i).band x⟩ := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    cases i using Fin.lastCases with
    | last =>
      simp only [serial, carrierEquiv, splitCarrier, Equiv.trans_apply,
        Equiv.sumCongr_apply, Equiv.coe_fn_mk, Equiv.refl_apply, Fin.lastCases_last, Sum.map_inr, Equiv.coe_trans, Function.comp_apply]
      apply joined_band_off
      exact fun h => hx (Sum.inr.inj h)
    | cast i =>
      let A := serial n (fun j => M j.castSucc) (fun j => c j.castSucc)
      let e := carrierEquiv n (fun j => M j.castSucc) (fun j => c j.castSucc)
      have hstep := ih (fun j => M j.castSucc) (fun j => c j.castSucc) i x hx
      have hnot : A.band (e ⟨i, x⟩) ≠ e ⟨i, x⟩ := by
        rw [hstep]
        intro h
        exact hx (eq_of_heq (Sigma.mk.inj (e.injective h)).2)
      simp only [carrierEquiv, Equiv.coe_trans, Function.comp_apply, splitCarrier, Fin.succ_last, Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, Equiv.sumCongr_apply, Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, Equiv.refl_apply]
      change joinedBand A (M (Fin.last (n + 1))) (c (Fin.last n))
        (Sum.inl (e ⟨i, x⟩)) = Sum.inl (e ⟨i, (M i.castSucc).band x⟩)
      rw [joined_band_off _ _ _ _ (fun h => hnot (Sum.inl.inj h))]
      exact congrArg Sum.inl hstep

private theorem connector_right (c : Perm (Fin 2)) (a : Fin 2) :
    connector c (Sum.inl (a.natAdd 2)) = Sum.inr ((c a).castAdd 2) := by
  rcases two_forms c with rfl | rfl
  all_goals fin_cases a <;> rfl

private theorem carrier_connector (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) (i : Fin n) (a : Fin 2) :
    (serial n M c).band
        (carrierEquiv n M c ⟨i.castSucc,
          ((M i.castSucc).ports (a.natAdd 2) : (M i.castSucc).Carrier)⟩) =
      carrierEquiv n M c ⟨i.succ,
        ((M i.succ).ports ((c i a).castAdd 2) : (M i.succ).Carrier)⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.lastCases with
    | last =>
      let A := serial n (fun j => M j.castSucc) (fun j => c j.castSucc)
      let e := carrierEquiv n (fun j => M j.castSucc) (fun j => c j.castSucc)
      simp only [carrierEquiv, Equiv.coe_trans, Function.comp_apply, splitCarrier, Fin.succ_last, Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, Equiv.sumCongr_apply, Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, Equiv.refl_apply]
      change joinedBand A (M (Fin.last (n + 1))) (c (Fin.last n))
        (Sum.inl (e ⟨Fin.last n,
          ((M (Fin.last n).castSucc).ports (a.natAdd 2) : _)⟩)) =
            Sum.inr ((M (Fin.last (n + 1))).ports (((c (Fin.last n)) a).castAdd 2) :
              (M (Fin.last (n + 1))).Carrier)
      rw [← carrier_right]
      have h := joined_band_at A (M (Fin.last (n + 1))) (c (Fin.last n))
        (Sum.inl (a.natAdd 2))
      simpa only [connector_right, sumPorts, Equiv.coe_fn_mk] using h
    | cast i =>
      let A := serial n (fun j => M j.castSucc) (fun j => c j.castSucc)
      let e := carrierEquiv n (fun j => M j.castSucc) (fun j => c j.castSucc)
      have hstep := ih (fun j => M j.castSucc) (fun j => c j.castSucc) i
      have hnot : A.band (e ⟨i.castSucc,
          ((M i.castSucc.castSucc).ports (a.natAdd 2) : _)⟩) ≠
          e ⟨i.castSucc, ((M i.castSucc.castSucc).ports (a.natAdd 2) : _)⟩ := by
        rw [hstep]
        intro h
        have hi := congrArg Sigma.fst (e.injective h)
        have hv := congrArg Fin.val hi
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      simp only [carrierEquiv, Equiv.coe_trans, Function.comp_apply, splitCarrier, Fin.succ_last, Fin.succ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last, Equiv.sumCongr_apply, Equiv.coe_fn_mk, Sum.map_inl, Sum.map_inr, Equiv.refl_apply]
      change joinedBand A (M (Fin.last (n + 1))) (c (Fin.last n))
        (Sum.inl (e ⟨i.castSucc, ((M i.castSucc.castSucc).ports (a.natAdd 2) : _)⟩)) =
          Sum.inl (e ⟨i.succ, ((M i.succ.castSucc).ports (((c i.castSucc) a).castAdd 2) : _)⟩)
      rw [joined_band_off _ _ _ _ (fun h => hnot (Sum.inl.inj h))]
      exact congrArg Sum.inl hstep

private def reindex (M : CutModule.{u}) {Y : Type u} [Finite Y]
    (e : Y ≃ M.Carrier) : CutModule.{u} where
  Carrier := Y
  finite := inferInstance
  corner := e.symm.permCongr M.corner
  band := e.symm.permCongr M.band
  corner_involutive := by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      M.corner_involutive, Equiv.symm_apply_apply]
    rw [M.corner_involutive, Equiv.symm_apply_apply]
  band_involutive := by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      M.band_involutive, Equiv.symm_apply_apply]
    rw [M.band_involutive, Equiv.symm_apply_apply]
  corner_free := by
    intro x h
    apply M.corner_free (e x)
    simpa only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply] using congrArg e h
  ports := M.ports.trans (e.symm.subtypeEquiv (by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
      e.symm.injective.eq_iff]))

private theorem reindex_pairing (M : CutModule.{u}) {Y : Type u} [Finite Y]
    (e : Y ≃ M.Carrier) : (M.reindex e).pairing = M.pairing := by
  have hc (i j : Fin 4) : (M.reindex e).pairing.SameCycle i j ↔ M.pairing.SameCycle i j := by
    rw [← (M.reindex e).cycle_iff, ← M.cycle_iff]
    change (e.symm.permCongr M.corner * e.symm.permCongr M.band).SameCycle
      (e.symm (M.ports i)) (e.symm (M.ports j)) ↔ _
    rw [← Equiv.permCongr_mul]
    exact same_cycle_perm_congr e.symm (M.corner * M.band) (M.ports i) (M.ports j)
  ext i
  have h := (hc i (M.pairing i)).mpr (Perm.SameCycle.refl M.pairing i).apply_right
  rw [same_cycle_involutive_iff _ (M.reindex e).pairing_involutive] at h
  exact congrArg Fin.val (h.resolve_left (fun hi => M.pairing_free i hi.symm))

/-- The actual chain on the original tagged carrier, with no compressed-away flags. -/
def serialOn (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) : CutModule.{u} :=
  (serial n M c).reindex (carrierEquiv n M c)

/-- The original-carrier serial construction preserves every corner and nonport band,
joins precisely adjacent right/left pairs, has the prescribed outer labels, and its
actual endpoint pairing is through exactly when all local actual pairings are through. -/
theorem serial_endpoint_pairing (n : ℕ) (M : Fin (n + 1) → CutModule.{u})
    (c : Fin n → Perm (Fin 2)) :
    (∀ i x, (serialOn n M c).corner ⟨i, x⟩ = ⟨i, (M i).corner x⟩) ∧
    (∀ i x, (M i).band x ≠ x → (serialOn n M c).band ⟨i, x⟩ = ⟨i, (M i).band x⟩) ∧
    (∀ (i : Fin n) (a : Fin 2),
      (serialOn n M c).band ⟨i.castSucc, ((M i.castSucc).ports (a.natAdd 2) : _)⟩ =
        ⟨i.succ, ((M i.succ).ports ((c i a).castAdd 2) : _)⟩) ∧
    (∀ a : Fin 2, ((serialOn n M c).ports (a.castAdd 2) : (serialOn n M c).Carrier) =
      ⟨0, ((M 0).ports (a.castAdd 2) : _)⟩) ∧
    (∀ a : Fin 2, ((serialOn n M c).ports (a.natAdd 2) : (serialOn n M c).Carrier) =
      ⟨Fin.last n, ((M (Fin.last n)).ports (a.natAdd 2) : _)⟩) ∧
    ((serialOn n M c).pairing ≠ thirdPairing ↔ ∀ i, (M i).pairing ≠ thirdPairing) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x
    apply (carrierEquiv n M c).injective
    change (carrierEquiv n M c) ((carrierEquiv n M c).symm
      ((serial n M c).corner (carrierEquiv n M c ⟨i, x⟩))) = _
    rw [Equiv.apply_symm_apply]
    exact carrier_corner n M c i x
  · intro i x hx
    apply (carrierEquiv n M c).injective
    change (carrierEquiv n M c) ((carrierEquiv n M c).symm
      ((serial n M c).band (carrierEquiv n M c ⟨i, x⟩))) = _
    rw [Equiv.apply_symm_apply]
    exact carrier_band_off n M c i x hx
  · intro i a
    apply (carrierEquiv n M c).injective
    change (carrierEquiv n M c) ((carrierEquiv n M c).symm
      ((serial n M c).band (carrierEquiv n M c ⟨i.castSucc,
        ((M i.castSucc).ports (a.natAdd 2) : _)⟩))) = _
    rw [Equiv.apply_symm_apply]
    exact carrier_connector n M c i a
  · intro a
    apply (carrierEquiv n M c).injective
    change (carrierEquiv n M c) ((carrierEquiv n M c).symm
      ((serial n M c).ports (a.castAdd 2) : (serial n M c).Carrier)) = _
    rw [Equiv.apply_symm_apply]
    exact carrier_left n M c a
  · intro a
    apply (carrierEquiv n M c).injective
    change (carrierEquiv n M c) ((carrierEquiv n M c).symm
      ((serial n M c).ports (a.natAdd 2) : (serial n M c).Carrier)) = _
    rw [Equiv.apply_symm_apply]
    exact carrier_right n M c a
  · rw [serialOn, reindex_pairing]
    exact serial_through n M c

end CutModule

#print axioms CutModule.serial_endpoint_pairing
end
end D5.S3.Combinatorics.PerfectMatchings.SerialEndpointPairing
