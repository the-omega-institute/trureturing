import D5.Scale38FirstExitProbe
open D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout leaves chi)
open ActualImageSevenLeafSeparation (leafAddresses leafLabel seven_leaf_separation)
open Scale38NestedCompensation (family query)
open RawEndpointPeeling (Peels)
set_option autoImplicit false
local notation "Index" => fun k : Nat => Unit ⊕ (Fin k ⊕ Fin k)
namespace PScanAttempt

def exitAt (k : Nat) : Index k → Nat
  | .inl _ => k+1
  | .inr (.inl j) => j.val
  | .inr (.inr i) => i.val+1

def replyAt {k : Nat} : Index k → Reply
  | .inr (.inr _) => .absent
  | _ => .branch

theorem attempt (k : Nat) (hk : 1 ≤ k) :
    let e := Fintype.equivFin (Index k)
    Peels (family k ∘ e.symm) (e (.inl ())) Finset.univ
      ((List.range (k+1)).map (query)) ∧
      ∀ U : Index k, U ≠ .inl () →
        ((List.range (k+1)).map (query)).find? (fun a => decide (chi (readout a (family k U)) = 1)) =
          some ((query) ((exitAt k) U)) := by
  classical
  let z : Index k := .inl ()
  let e := Fintype.equivFin (Index k)
  let F := family k ∘ e.symm
  have base := Scale38NestedCompensation.result k hk
  have rawP := base.2.2.2.2.1
  have rawX := base.2.2.2.2.2.1
  have rawY := base.2.2.2.2.2.2.1
  have target_leaf (t : Nat) (ht : t < k+1) :
      query t ∈ leaves (family k z) ∧ chi (readout (query t) (family k z)) = 0 := by
    have hr : readout (query t) (family k z) = .alpha := rawP t (by omega)
    have hm := ((seven_leaf_separation.1 (family k z)).2 (query t)).mpr
      ⟨true, by simp only [leafLabel, hr]⟩
    exact ⟨by simpa only [leafAddresses, List.mem_toFinset] using hm, by rw [hr]; rfl⟩
  have before (U : Index k) (t : Nat) (ht : t < k+1) (hb : t < exitAt k U) :
      readout (query t) (family k U) = readout (query t) (family k z) := by
    rw [rawP t (by omega)]
    cases U with
    | inl u => exact rawP t (by omega)
    | inr v => cases v with
      | inl j => exact (rawX j).1 t hb
      | inr i => exact (rawY i).1 t (by change t < i.val+1 at hb; omega)
  have exiting (U : Index k) (hu : U ≠ z) : exitAt k U < k+1 ∧
      readout (query (exitAt k U)) (family k U) = replyAt U := by
    cases U with
    | inl u => cases u; exact (hu rfl).elim
    | inr v => cases v with
      | inl j => exact ⟨by change j.val < k+1; omega, (rawX j).2⟩
      | inr i => exact ⟨by change i.val+1 < k+1; omega, (rawY i).2⟩
  have unique (U V : Index k) (hu : U ≠ z) (hv : V ≠ z)
      (he : exitAt k U = exitAt k V)
      (hr : readout (query (exitAt k U)) (family k U) =
        readout (query (exitAt k V)) (family k V)) : U = V := by
    rw [(exiting U hu).2, (exiting V hv).2] at hr
    cases U with
    | inl u => cases u; exact (hu rfl).elim
    | inr u => cases V with
      | inl v => cases v; exact (hv rfl).elim
      | inr v =>
        cases u <;> cases v <;> simp only [replyAt] at hr
        all_goals try cases hr
        all_goals congr 2
        all_goals apply Fin.ext
        all_goals simp only [exitAt] at he
        all_goals omega
  constructor
  ·
    change Peels F (e z) Finset.univ _
    apply safe_scan F (e z) query (fun j => exitAt k (e.symm j))
    · simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using target_leaf
    · intro j t ht hb
      exact (before (e.symm j) t ht hb).trans (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply])
    · intro j hj
      have hn : e.symm j ≠ z := by
        intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
      have hx := exiting (e.symm j) hn
      refine ⟨hx.1, ?_⟩
      change chi (readout (query (exitAt k (e.symm j))) (family k (e.symm j))) = 1
      rw [hx.2]
      generalize e.symm j = U
      cases U with
      | inl u => rfl
      | inr v => cases v <;> rfl
    · intro a b ha hb he hr
      apply e.symm.injective
      apply unique (e.symm a) (e.symm b)
      · intro h; apply ha; exact (e.apply_symm_apply a).symm.trans (congrArg e h)
      · intro h; apply hb; exact (e.apply_symm_apply b).symm.trans (congrArg e h)
      · exact he
      · exact hr
  · intro U hu
    have hfirst := first_exit F (e z) (e U) (query) (fun j => (exitAt k) (e.symm j))
      (fun h => hu (e.injective h))
      (fun t ht => by simpa only [F, Function.comp_apply, Equiv.symm_apply_apply]
        using (target_leaf t ht).2)
      (fun j t ht hb => (before (e.symm j) t ht hb).trans
        (by simp only [F, Function.comp_apply, Equiv.symm_apply_apply]))
      (fun j hj => by
        have hn : e.symm j ≠ z := by
          intro h; apply hj; exact (e.apply_symm_apply j).symm.trans (congrArg e h)
        have hx := exiting (e.symm j) hn
        refine ⟨hx.1, ?_⟩
        change chi (readout ((query) ((exitAt k) (e.symm j))) (family k (e.symm j))) = 1
        rw [hx.2]
        generalize e.symm j = V
        cases V with
        | inl u => rfl
        | inr v =>
          cases v <;> rfl
      )
    simpa only [F, Function.comp_apply, Equiv.symm_apply_apply] using hfirst

end PScanAttempt
