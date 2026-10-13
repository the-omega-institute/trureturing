/- GID: D5/S3/Geometry/Gluing/ActualLinkAffineFan
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/ActualLinkAffineFan
   mirror-E: none(waiver:actual-strict-affine-coordinates)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Strict affine sectors parametrize the actual ordered-corner neighborhood. -/

import D5.S3.Geometry.Gluing.ActualCornerPointPeriods

set_option autoImplicit false
noncomputable section
open scoped BigOperators Fin.NatCast
namespace D5.S3.Geometry.Gluing.ActualLinkAffineFan
open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Gluing.ActualCornerPointPeriods

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

/-- The radial cutoff is strict; the cutoff boundary remains in the ambient carrier. -/
abbrev Sector := {p : ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 < 1}

/-- Incoming and outgoing face coordinates retain their source ordering. -/
def beta (c : Fin 4) (s : Fin 3) (p : ℝ × ℝ) (l : Fin 4) : ℝ :=
  if l = tip c s then 1 - (p.1 + p.2) / 2
  else if l = incoming c s then p.1 / 2
  else if l = outgoing c s then p.2 / 2 else 0

private theorem beta_values (c : Fin 4) (s : Fin 3) (p : ℝ × ℝ) :
    beta c s p (corner c s) = 0 ∧
    beta c s p (tip c s) = 1 - (p.1 + p.2) / 2 ∧
    beta c s p (incoming c s) = p.1 / 2 ∧
    beta c s p (outgoing c s) = p.2 / 2 := by
  fin_cases c <;> fin_cases s <;> simp [beta,corner,tip,incoming,outgoing]

private theorem beta_simplex (c : Fin 4) (s : Fin 3) (p : Sector) :
    (∀ l, 0 ≤ beta c s p.val l) ∧
    (∑ l, beta c s p.val l) = 1 ∧ 1 / 2 < beta c s p.val (tip c s) := by
  obtain ⟨ha,hb,hs⟩ := p.property
  have hv := beta_values c s p.val
  refine ⟨?_, ?_, by rw [hv.2.1]; linarith⟩
  · intro l
    unfold beta
    split_ifs <;> linarith
  · fin_cases c <;> fin_cases s <;>
      simp [Fin.sum_univ_succ,beta,tip,incoming,outgoing] <;> ring

private theorem dart_label (u v : G) {d e : Dart Ω} (h : DartRelated u v d e) :
    label (pairing u v) d.1 = label (pairing u v) e.1 := by
  induction h with
  | rel d e h =>
    obtain ⟨f,hfj,_,rfl⟩ := h
    let P : Point u v (label (pairing u v) d.1) :=
      ⟨(d.1,fun l => if l = d.1.2 + 1 then 1 else 0),by
        refine ⟨?_,?_,?_,rfl⟩
        · have hj : d.1.2 ≠ d.1.2 + 1 := by
            generalize d.1.2 = j
            fin_cases j <;> decide
          simp [hj]
        · intro l; dsimp; split_ifs <;> norm_num
        · simp⟩
    exact (pairedPoint u v P f hfj).property.2.2.2.symm
  | refl d => rfl
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The same actual corner class as the phase-zero seed. -/
def vertex (u v : G) (c : Fin 4) (x : Ω) : Vertex (pairing (Ω := Ω) u v) :=
  label (pairing u v) (encode u v c (x,0)).1

/-- The actual finite occurrence, with affine coordinates on its original face array. -/
def rawPhi (u v : G) (c : Fin 4) (x : Ω)
    (z : Fin (3 * pointPeriod u v c x) × Sector) : Raw Ω :=
  ((occurrence u v c x z.1).1,
    beta c ((tour u v c)^[z.1.val] (x,0)).2 z.2.val)

private theorem rawPhi_mem (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z : Fin (3 * pointPeriod u v c x) × Sector) :
    rawPhi u v c x z ∈ Carrier u v (vertex u v c x) := by
  have hv := beta_values c ((tour u v c)^[z.1.val] (x,0)).2 z.2.val
  have hs := beta_simplex c ((tour u v c)^[z.1.val] (x,0)).2 z.2
  refine ⟨hv.1,hs.1,hs.2.1,?_⟩
  exact (dart_label u v (((actual_component_enumeration u v c x).2.2.1 _).mpr
    ⟨z.1,rfl⟩)).symm

/-- The constructed strict-sector map into the genuine source neighborhood. -/
def Phi (u v : G) (c : Fin 4) (x : Ω) [Finite Ω]
    (z : Fin (3 * pointPeriod u v c x) × Sector) :
    ↥(Neighborhood u v (ν := vertex u v c x) (encode u v c (x,0))) :=
  ⟨⟨rawPhi u v c x z, rawPhi_mem u v c x z⟩,
    (occurrence u v c x z.1).2,
    (beta_simplex c ((tour u v c)^[z.1.val] (x,0)).2 z.2).2.2,
    ((actual_component_enumeration u v c x).2.2.1 _).mpr ⟨z.1,rfl⟩⟩

private theorem dominant_unique (b : Fin 4 → ℝ) (hn : ∀ l, 0 ≤ b l)
    (hs : (∑ l, b l) = 1) {k l : Fin 4} (hk : 1 / 2 < b k) (hl : 1 / 2 < b l) :
    k = l := by
  classical
  by_contra hne
  have hp := Finset.sum_le_sum_of_subset_of_nonneg
    (f := b) (Finset.subset_univ ({k,l} : Finset (Fin 4)))
    (by intro i _ _; exact hn i)
  simp [hne,hs] at hp
  linarith

private theorem inverse_sector (c : Fin 4) (s : Fin 3) (b : Fin 4 → ℝ)
    (hj : b (corner c s) = 0) (hn : ∀ l, 0 ≤ b l)
    (hs : (∑ l, b l) = 1) (hk : 1 / 2 < b (tip c s)) :
    (0 ≤ 2*b (incoming c s) ∧ 0 ≤ 2*b (outgoing c s) ∧
      2*b (incoming c s) + 2*b (outgoing c s) < 1) ∧
    beta c s (2*b (incoming c s),2*b (outgoing c s)) = b := by
  have h0 := hn 0; have h1 := hn 1; have h2 := hn 2; have h3 := hn 3
  constructor
  · refine ⟨mul_nonneg (by norm_num) (hn _),mul_nonneg (by norm_num) (hn _),?_⟩
    fin_cases c <;> fin_cases s <;>
      simp [corner,tip,incoming,outgoing,Fin.sum_univ_succ] at * <;> linarith
  · funext l
    fin_cases c <;> fin_cases s <;> fin_cases l <;>
      simp [beta,corner,tip,incoming,outgoing,Fin.sum_univ_succ] at * <;> linarith

/-- Every strict original representative has unique actual occurrence and affine coordinates. -/
theorem actual_strict_coordinates (u v : G) (c : Fin 4) (x : Ω) [Finite Ω] :
    Function.Bijective (Phi u v c x) := by
  constructor
  · rintro ⟨i,p⟩ ⟨j,q⟩ h
    have hr : rawPhi u v c x (i,p) = rawPhi u v c x (j,q) :=
      congrArg (fun z => z.val.val) h
    have ht := congrArg Prod.fst hr
    have hb := congrArg Prod.snd hr
    have hpi := beta_simplex c ((tour u v c)^[i.val] (x,0)).2 p
    have hpj := beta_simplex c ((tour u v c)^[j.val] (x,0)).2 q
    have hk : (occurrence u v c x i).2 = (occurrence u v c x j).2 := by
      apply dominant_unique _ hpi.1 hpi.2.1 hpi.2.2
      change beta c ((tour u v c)^[i.val] (x,0)).2 p.val _ > 1 / 2
      change beta c ((tour u v c)^[i.val] (x,0)).2 p.val =
        beta c ((tour u v c)^[j.val] (x,0)).2 q.val at hb
      rw [hb]
      exact hpj.2.2
    have hij := (actual_component_enumeration u v c x).2.1 (Prod.ext ht hk)
    change i = j at hij
    subst j
    have hp := beta_values c ((tour u v c)^[i.val] (x,0)).2 p.val
    have hq := beta_values c ((tour u v c)^[i.val] (x,0)).2 q.val
    have ha := congrFun hb (incoming c ((tour u v c)^[i.val] (x,0)).2)
    have hb' := congrFun hb (outgoing c ((tour u v c)^[i.val] (x,0)).2)
    change beta _ _ _ _ = beta _ _ _ _ at ha hb'
    rw [hp.2.2.1,hq.2.2.1] at ha
    rw [hp.2.2.2,hq.2.2.2] at hb'
    have hpq : p = q := Subtype.ext (Prod.ext (by linarith) (by linarith))
    subst q
    rfl
  · intro y
    obtain ⟨k,hk,hd⟩ := y.property
    obtain ⟨i,hi⟩ := ((actual_component_enumeration u v c x).2.2.1 _).mp hd
    have hj := congrArg (fun d : Dart Ω => d.1.2) hi
    have ht := congrArg Prod.snd hi
    let s := ((tour u v c)^[i.val] (x,0)).2
    have hy := y.val.property
    change corner c s = y.val.val.1.2 at hj
    change tip c s = k at ht
    have hzero : y.val.val.2 (corner c s) = 0 := by rw [hj]; exact hy.1
    have hdom : 1 / 2 < y.val.val.2 (tip c s) := by rw [ht]; exact hk
    obtain ⟨hab,hbeta⟩ := inverse_sector c s y.val.val.2 hzero hy.2.1 hy.2.2.1 hdom
    let p : Sector := ⟨(2*y.val.val.2 (incoming c s),2*y.val.val.2 (outgoing c s)),hab⟩
    refine ⟨(i,p),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change rawPhi u v c x (i,p) = y.val.val
    apply Prod.ext
    · exact congrArg (fun d : Dart Ω => d.1) hi
    · exact hbeta

end D5.S3.Geometry.Gluing.ActualLinkAffineFan
