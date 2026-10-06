/- GID: D5/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection
   mirror-E: none(waiver:unbounded-marked-prefix-arithmetic)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.marked_prefix_rigidity_and_charge; instance=D5/S1/Words/Palindromes/PeriodDoubling/BaseCertificates.baseTable
   digest: Raw marker paths project to indexed base paths and preserve signed digits. -/

/-
proof_shape: content (marker_base_projection)
escape_witness: Path induction follows selected transitions and preserves every emitted signed digit.
admission_basis: escape-witness
Direct frozen dependencies: none; imported period-doubling modules are delivered together.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.PrefixPathRealization
import D5.S1.Words.Palindromes.PeriodDoubling.BaseSignedStreams
namespace D5.S1.Words.Palindromes.PeriodDoubling

open BaseCertificates MarkedPrefixCertificates
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem marker_base_projection (charge : Bool) {s t : List ℤ}
    {xs : List (ℤ × ℤ × ℤ × ℤ)} (p : prefixRawAutomaton.Path s t xs)
    (u : Fin 1492) (hs : s[0]?.getD 0=(u.val : ℤ)) :
    ∃ (v : Fin 1492) (q : (baseAutomaton charge).Path u v xs),
      t[0]?.getD 0=(v.val : ℤ) ∧
      ∀ output : Bool,
        pathOutputs (fun _ _ (r : List ℤ) =>
          (baseTable (r[0]?.getD 0).toNat).1[if output then 12 else 10]?.getD 0) p =
        pathOutputs (fun _ _ (r : Fin 1492) =>
          (baseTable r.val).1[if output then 12 else 10]?.getD 0) q := by
  have checked : ∀ u : Fin 1492, (baseTable u.val).2.1.all (fun e => decide (e.1<1492))=true := by
    have blocks : ∀ b : Fin 47,
      (List.range (min 32 (1492-32*b.val))).all (fun k =>
        (baseTable (32*b.val+k)).2.1.all (fun e => decide (e.1<1492)))=true := by
      intro b;fin_cases b <;> decide
    intro u
    have hb:=blocks ⟨u.val/32,by omega⟩
    have hk : u.val%32 ∈ List.range (min 32 (1492-32*(u.val/32))) := by
      simp only [List.mem_range];omega
    simpa only [show 32*(u.val/32)+u.val%32=u.val by omega] using List.all_eq_true.mp hb _ hk
  have step {s q : List ℤ} {a : ℤ × ℤ × ℤ × ℤ}
      (he : (q,a) ∈ successors s) (u : Fin 1492) (hs : s[0]?.getD 0=(u.val : ℤ)) :
      ∃ v : Fin 1492, q[0]?.getD 0=(v.val : ℤ) ∧ v ∈ (baseAutomaton charge).step u a := by
    obtain ⟨e,he,hmem⟩:=List.mem_flatMap.mp he
    have he' : e ∈ (baseTable u.val).2.1 := by simpa only [hs,Int.toNat_natCast] using he
    have hv : e.1<1492 := of_decide_eq_true (List.all_eq_true.mp (checked u) e he')
    have hq : q[0]?.getD 0=(e.1 : ℤ) ∧ e.2=a := by
      unfold nextMarker at hmem
      dsimp only at hmem
      split at hmem
      · simp at hmem
      · split at hmem
        · split at hmem
          · simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl,ha⟩ | ⟨rfl,ha⟩ <;> exact ⟨rfl,ha.symm⟩
          · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
            obtain ⟨rfl,ha⟩:=hmem;exact ⟨rfl,ha.symm⟩
        · split at hmem
          · split at hmem
            · simp at hmem
            · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
              obtain ⟨rfl,ha⟩:=hmem;exact ⟨rfl,ha.symm⟩
          · split at hmem
            · split at hmem
              · simp at hmem
              · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
                obtain ⟨rfl,ha⟩:=hmem;exact ⟨rfl,ha.symm⟩
            · split at hmem
              · simp at hmem
              · simp only [List.mem_singleton,Prod.mk.injEq] at hmem
                obtain ⟨rfl,ha⟩:=hmem;exact ⟨rfl,ha.symm⟩
    refine ⟨⟨e.1,hv⟩,hq.1,?_⟩
    change (e.1,a) ∈ (baseTable u.val).2.1
    rw [← hq.2];exact he'
  induction p generalizing u with
  | nil s => exact ⟨u,.nil u,hs,fun _ => rfl⟩
  | cons r s t a xs he p ih =>
    obtain ⟨v,hv,hstep⟩:=step he u hs
    obtain ⟨w,q,hw,hout⟩:=ih v hv
    refine ⟨w,.cons v u w a xs hstep q,hw,?_⟩
    intro output
    simp only [pathOutputs,hv,Int.toNat_natCast,hout]
end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.marker_base_projection
