import D5.S3.Geometry.Gluing.ActualLinkCyclicPresentation
import D5.S3.Geometry.Gluing.CyclicP2CoherentOrientation

set_option autoImplicit false
noncomputable section

namespace CFMPActualLinkCoherentExactCheck

open D5.S3.Geometry.Hyperideal.ActualCornerTransport
open D5.S3.Geometry.Hyperideal.NoncommutativeCornerOrbits
open D5.S3.Geometry.Gluing.ActualLinkCornerChains
open D5.S3.Geometry.Gluing.ActualEndpointReturnClasses
open D5.S3.Geometry.Gluing.ActualLinkCyclicPresentation
open D5.S3.Geometry.Gluing.CyclicP1GeneratedVertices
open D5.S3.Geometry.Gluing.CyclicP2GeneratedVertices.FullCut
open D5.S3.Geometry.Gluing.CyclicP2CoherentOrientation

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]
variable {u v : G} {ν : Vertex (pairing (Ω := Ω) u v)}
variable {P : FiniteCyclicPresentation}

private abbrev ActualFace (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  ActualLinkCyclicPresentation.Face u v ν

private abbrev ActualSide (u v : G) (ν : Vertex (pairing (Ω := Ω) u v)) :=
  ActualLinkCyclicPresentation.Side u v ν

private def cornerParity (j : Fin 4) : Bool := decide (j.val % 2 = 1)

private def faceChoice (fe : ActualFace u v ν ≃ Fin P.faces.length)
    (f : CyclicP2GeneratedVertices.FullCut.Face P) : Bool :=
  cornerParity (fe.symm f).val.2

/-- The actual endpoint permutation compensates the change of corner parity. -/
private theorem corner_parity_flip
    (flip : ActualSide u v ν → Bool)
    (htransport : ∀ (s : ActualSide u v ν) (b : Bool),
      (sideFlag u v (pairedSide u v s) (Bool.xor b (flip s))).val =
        dartMove u v s.val.2 (sideFlag u v s b).val)
    (s : ActualSide u v ν) :
    Bool.xor
      (Bool.xor (cornerParity s.val.1.2)
        (cornerParity (pairedSide u v s).val.1.2))
      (flip s) = true := by
  have hv := congrArg (fun z : Dart Ω => z.2) (htransport s false)
  rcases s with ⟨⟨⟨t, j⟩, f⟩, hfj, hν⟩
  cases hbit : flip (⟨⟨⟨t, j⟩, f⟩, hfj, hν⟩ : ActualSide u v ν) <;>
    simp only [hbit, Bool.false_xor] at hv
  all_goals fin_cases j <;> fin_cases f
  all_goals first
    | decide
    | exact False.elim ((show ¬ (type_of% hfj) from by decide) hfj)
    | exact False.elim ((show ¬ (type_of% hv) from by decide) hv)

/-- Read the endpoint bit before passing to any vertex quotient. -/
private theorem endpoint_sign_relation
    (dart : ActualSide u v ν → SignedDart (Fin P.edgeCount))
    (flip : ActualSide u v ν → Bool)
    (hendpoint : ∀ (s : ActualSide u v ν) (b : Bool),
      (if Bool.xor b (flip s) then terminal (dart (pairedSide u v s))
        else initial (dart (pairedSide u v s))) =
      (if b then terminal (dart s) else initial (dart s)))
    (s : ActualSide u v ν) :
    Bool.xor (flip s) (sign (dart (pairedSide u v s))) = sign (dart s) := by
  have hsnd := congrArg Prod.snd (hendpoint s false)
  cases hf : flip s <;> cases hd : dart s <;> cases hp : dart (pairedSide u v s) <;>
    simp_all [initial, terminal, sign, Bool.xor]

private theorem faceSide_injective (u v : G)
    {ν : Vertex (pairing (Ω := Ω) u v)}
    {c c' : ActualFace u v ν} {i j : Fin 3}
    (h : faceSide u v c i = faceSide u v c' j) : c = c' ∧ i = j := by
  have hc : c.val = c'.val := congrArg (fun s : ActualSide u v ν => s.val.1) h
  have hcc : c = c' := Subtype.ext hc
  subst c'
  have hv := congrArg (fun s : ActualSide u v ν => s.val.2) h
  change faceVertex c.val.2 i = faceVertex c.val.2 j at hv
  rcases c with ⟨⟨t, f⟩, hν⟩
  fin_cases f <;> fin_cases i <;> fin_cases j <;>
    simp [faceVertex] at hv ⊢

private def occurrenceOf
    (P : FiniteCyclicPresentation)
    (fe : ActualFace u v ν ≃ Fin P.faces.length)
    (dart : ActualSide u v ν → SignedDart (Fin P.edgeCount))
    (hfaces : ∀ c : ActualFace u v ν, P.faces.get (fe c) =
      [dart (faceSide u v c 0), dart (faceSide u v c 1),
        dart (faceSide u v c 2)])
    (c : ActualFace u v ν) (i : Fin 3) : Occurrence P :=
  ⟨fe c, Fin.cast (by
    simpa using (congrArg List.length (hfaces c)).symm) i⟩

private theorem occurrence_decompose
    (P : FiniteCyclicPresentation)
    (fe : ActualFace u v ν ≃ Fin P.faces.length)
    (dart : ActualSide u v ν → SignedDart (Fin P.edgeCount))
    (hfaces : ∀ c : ActualFace u v ν, P.faces.get (fe c) =
      [dart (faceSide u v c 0), dart (faceSide u v c 1),
        dart (faceSide u v c 2)])
    (o : Occurrence P) :
    ∃ (c : ActualFace u v ν) (i : Fin 3),
      o = occurrenceOf P fe dart hfaces c i ∧
        CyclicP2CoherentOrientation.dart P o = dart (faceSide u v c i) := by
  let c := fe.symm o.1
  have hc : fe c = o.1 := fe.apply_symm_apply _
  have hi : o.2.val < 3 := by
    have h := o.2.isLt
    change o.2.val < (P.faces.get o.1).length at h
    rw [← hc, hfaces c] at h
    exact h
  let i : Fin 3 := ⟨o.2.val, hi⟩
  have ho : o = occurrenceOf P fe dart hfaces c i := by
    apply Sigma.ext hc.symm
    apply (Fin.heq_ext_iff
      (congrArg (fun f : CyclicP2GeneratedVertices.FullCut.Face P => (boundary P f).length)
        hc.symm)).mpr
    rfl
  refine ⟨c, i, ho, ?_⟩
  rw [ho]
  fin_cases i <;>
    simp [CyclicP2CoherentOrientation.dart, boundary, occurrenceOf, hfaces,
      List.get_eq_getElem]

private theorem coherent_choices_of_actual
    (P : FiniteCyclicPresentation)
    (fe : ActualFace u v ν ≃ Fin P.faces.length)
    (name : ActualSide u v ν → Fin P.edgeCount)
    (dart : ActualSide u v ν → SignedDart (Fin P.edgeCount))
    (flip : ActualSide u v ν → Bool)
    (hfaces : ∀ c : ActualFace u v ν, P.faces.get (fe c) =
      [dart (faceSide u v c 0), dart (faceSide u v c 1),
        dart (faceSide u v c 2)])
    (hedge : ∀ s : ActualSide u v ν, (dart s).edge = name s)
    (hname : ∀ s t : ActualSide u v ν,
      name s = name t ↔ t = s ∨ t = pairedSide u v s)
    (htransport : ∀ (s : ActualSide u v ν) (b : Bool),
      (sideFlag u v (pairedSide u v s) (Bool.xor b (flip s))).val =
        dartMove u v s.val.2 (sideFlag u v s b).val)
    (hendpoint : ∀ (s : ActualSide u v ν) (b : Bool),
      (if Bool.xor b (flip s) then terminal (dart (pairedSide u v s))
        else initial (dart (pairedSide u v s))) =
      (if b then terminal (dart s) else initial (dart s))) :
    Coh P := by
  refine ⟨faceChoice (P := P) fe, ?_⟩
  intro o o' hoo he
  obtain ⟨c, i, ho, hdo⟩ := occurrence_decompose P fe dart hfaces o
  obtain ⟨c', j, ho', hdo'⟩ := occurrence_decompose P fe dart hfaces o'
  have hsne : faceSide u v c i ≠ faceSide u v c' j := by
    intro hs
    apply hoo
    rw [ho, ho']
    obtain ⟨hcc, hij⟩ := faceSide_injective u v hs
    subst c'
    subst j
    rfl
  let s := faceSide u v c i
  let t := faceSide u v c' j
  have hnameeq : name s = name t := by
    calc
      name s = (dart s).edge := (hedge s).symm
      _ = (CyclicP2CoherentOrientation.dart P o).edge :=
        (congrArg SignedDart.edge hdo).symm
      _ = (CyclicP2CoherentOrientation.dart P o').edge := he
      _ = (dart t).edge := congrArg SignedDart.edge hdo'
      _ = name t := hedge t
  have hpaired : t = pairedSide u v s := by
    rcases (hname s t).mp hnameeq with hst | hst
    · exact False.elim (hsne hst.symm)
    · exact hst
  have hparity := corner_parity_flip (u := u) (v := v) (ν := ν) flip htransport s
  have hsign := endpoint_sign_relation (P := P) (u := u) (v := v)
    (ν := ν) dart flip hendpoint s
  have hsource : cornerParity s.val.1.2 = faceChoice (P := P) fe (fe c) := by
    simp only [faceChoice, Equiv.symm_apply_apply]
    rfl
  have htarget : cornerParity (pairedSide u v s).val.1.2 =
      faceChoice (P := P) fe (fe c') := by
    rw [← hpaired]
    simp only [faceChoice, Equiv.symm_apply_apply]
    rfl
  rw [hsource, htarget] at hparity
  change Bool.xor (faceChoice (P := P) fe o.1)
      (sign (CyclicP2CoherentOrientation.dart P o)) ≠
    Bool.xor (faceChoice (P := P) fe o'.1)
      (sign (CyclicP2CoherentOrientation.dart P o'))
  rw [hdo, hdo']
  change Bool.xor (faceChoice (P := P) fe o.1) (sign (dart s)) ≠
    Bool.xor (faceChoice (P := P) fe o'.1) (sign (dart t))
  have hof : o.1 = fe c := congrArg Sigma.fst ho
  have hof' : o'.1 = fe c' := congrArg Sigma.fst ho'
  rw [hof, hof', hpaired]
  cases hfc : faceChoice (P := P) fe (fe c) <;>
    cases hfp : faceChoice (P := P) fe (fe c') <;>
    cases hflip : flip s <;>
    cases hsd : sign (dart s) <;>
    cases hsp : sign (dart (pairedSide u v s)) <;>
    simp_all [Bool.xor]

example (u v : G)
    [Finite Ω] (ν : Vertex (pairing (Ω := Ω) u v)) :
    ∃ (P : FiniteCyclicPresentation)
      (facepositionequiv : ActualFace u v ν ≃ Fin P.faces.length)
      (name : ActualSide u v ν → Fin P.edgeCount)
      (dart : ActualSide u v ν → SignedDart (Fin P.edgeCount))
      (flip : ActualSide u v ν → Bool)
      (vertices : Vertices P ≃ FlagQuotient u v ν),
      (∀ c : ActualFace u v ν, P.faces.get (facepositionequiv c) =
        [dart (faceSide u v c 0), dart (faceSide u v c 1),
          dart (faceSide u v c 2)]) ∧
      (∀ i : Fin P.faces.length, (P.faces.get i).length = 3) ∧
      (∀ e : Fin P.edgeCount, Occurs P e) ∧
      (∀ s : ActualSide u v ν, (dart s).edge = name s) ∧
      (∀ s t : ActualSide u v ν,
        name s = name t ↔ t = s ∨ t = pairedSide u v s) ∧
      (Function.Involutive (pairedSide u v (ν := ν))) ∧
      (∀ s : ActualSide u v ν, pairedSide u v s ≠ s) ∧
      (∀ (s : ActualSide u v ν) (b : Bool),
        (sideFlag u v (pairedSide u v s) (Bool.xor b (flip s))).val =
          dartMove u v s.val.2 (sideFlag u v s b).val) ∧
      (∀ (s : ActualSide u v ν) (t : ℝ),
        move u v s.val.2 (sideParameter u v s t) =
          sideParameter u v (pairedSide u v s)
            (if flip s then 1 - t else t)) ∧
      (∀ (s : ActualSide u v ν) (b : Bool),
        (if Bool.xor b (flip s) then terminal (dart (pairedSide u v s))
          else initial (dart (pairedSide u v s))) =
        (if b then terminal (dart s) else initial (dart s))) ∧
      (∀ s : ActualSide u v ν,
        vertices (Quotient.mk _ (initial (dart s))) =
            Quotient.mk _ (sideFlag u v s false) ∧
        vertices (Quotient.mk _ (terminal (dart s))) =
            Quotient.mk _ (sideFlag u v s true)) ∧
      Coh P := by
  rcases actual_link_cyclic_vertices u v ν with
    ⟨P, facepositionequiv, name, dart, flip, vertices,
      hfaces, hlen, hocc, hedge, hname, hinv, hne, htransport,
      hparameter, hendpoint, hvertices⟩
  refine ⟨P, facepositionequiv, name, dart, flip, vertices,
    hfaces, hlen, hocc, hedge, hname, hinv, hne, htransport,
    hparameter, hendpoint, hvertices, ?_⟩
  exact coherent_choices_of_actual P facepositionequiv name dart flip
    hfaces hedge hname htransport hendpoint

end CFMPActualLinkCoherentExactCheck
