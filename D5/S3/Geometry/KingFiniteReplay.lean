/- GID: D5/S3/Geometry/KingFiniteReplay
   generality: I
   mirror-B: D5/B/S3/Geometry/KingFiniteReplay
   mirror-E: none(waiver:finite-graph-singular-homology)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Subgraph]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Geometry/KingFinalComposition.routeBaseReducedHomologyIso; premises=D5/S3/Geometry/KingFiniteReplay.adjacency39
   digest: The exact forty-move chain from the actual graph6-complement seed to the 141-vertex labeled graph. -/
import D5.S3.Geometry.KingFiniteReplay.Data
import D5.S3.Geometry.KingFiniteReplay.TripleReplay
/-!
# Forty concrete suspensions of the torsion seed

The exact natural labels, edge operations and neighborhood partitions come
from graph-construction.json, SHA-256
ff9876310835eca475074719e41da20ea0d5056d76b996c3ea7d5b63fcaa0980.
The initial graph is the complement of graph6 JEhbtj{rve?. Ten triple
subdivisions, five matching suspensions and twenty-five Lozin replacements
produce the literal 141-vertex, 178-edge endpoint. The matching and star
subgraphs are arbitrary local subgraphs, so extra ambient edges are retained.
Barmak, Proposition 7.2, and Biyikoglu--Civan, Proposition 3.4, provide the
classical suspension mechanisms.
-/
noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

open CategoryTheory

namespace D5.S3.Geometry.KingFiniteReplay

open FiniteGraphSuspensionMoves

/- Certificate operation 10 (0-based): crossing_suspension. -/
def ends10 : (Bool × Bool) ↪ Vertex10 where
  toFun p := if p.1 then (if p.2 then ⟨20, by decide⟩ else ⟨1, by decide⟩)
    else (if p.2 then ⟨14, by decide⟩ else ⟨13, by decide⟩)
  inj' := by decide
theorem edge10a : graph10.Adj (ends10 (false, false)) (ends10 (false, true)) := by decide
theorem edge10b : graph10.Adj (ends10 (true, false)) (ends10 (true, true)) := by decide
def oldLabel10 : (Vertex10) → ℕ := fun x => x.val
def newLabel10 : Option (Bool × Bool) → ℕ := fun p => match p with
  | none => 41
  | some p => if p.1 then (if p.2 then 45 else 44)
      else (if p.2 then 43 else 42)
theorem newLabel10_injective : Function.Injective newLabel10 := by decide
theorem fresh10 : ∀ o : Vertex10, ∀ a : Option (Bool × Bool), oldLabel10 o ≠ newLabel10 a := by decide
theorem labels10_mem : ∀ a : (Vertex10) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel10 newLabel10 a ∈ vertices11 := by decide
theorem labels10_cover : ∀ t : Vertex11, ∃ a : (Vertex10) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel10 newLabel10 a = t.val := by decide
def labels10 : ((Vertex10) ⊕ (Option (Bool × Bool))) ≃ Vertex11 :=
  sumLabels vertices11 oldLabel10 newLabel10 (Subtype.val_injective)
    newLabel10_injective fresh10 labels10_mem labels10_cover
theorem adjacency10 : ∀ x y : (Vertex10) ⊕ (Option (Bool × Bool)),
    graph11.Adj (labels10 x) (labels10 y) ↔ (crossingSuspension graph10 ends10).Adj x y := by decide
theorem mappedGraph10 : (crossingSuspension graph10 ends10).map labels10 = graph11 :=
  map_eq_of_forward (crossingSuspension graph10 ends10) graph11 labels10 adjacency10
def chain11 : MoveChain IndependenceComplexTorsionSeed.G0 graph11 11 := by
  simpa only [mappedGraph10] using (MoveChain.crossing chain10 ends10 edge10a edge10b labels10)

/- Certificate operation 11 (0-based): crossing_suspension. -/
def ends11 : (Bool × Bool) ↪ Vertex11 where
  toFun p := if p.1 then (if p.2 then ⟨23, by decide⟩ else ⟨1, by decide⟩)
    else (if p.2 then ⟨11, by decide⟩ else ⟨0, by decide⟩)
  inj' := by decide
theorem edge11a : graph11.Adj (ends11 (false, false)) (ends11 (false, true)) := by decide
theorem edge11b : graph11.Adj (ends11 (true, false)) (ends11 (true, true)) := by decide
def oldLabel11 : (Vertex11) → ℕ := fun x => x.val
def newLabel11 : Option (Bool × Bool) → ℕ := fun p => match p with
  | none => 46
  | some p => if p.1 then (if p.2 then 50 else 49)
      else (if p.2 then 48 else 47)
theorem newLabel11_injective : Function.Injective newLabel11 := by decide
theorem fresh11 : ∀ o : Vertex11, ∀ a : Option (Bool × Bool), oldLabel11 o ≠ newLabel11 a := by decide
theorem labels11_mem : ∀ a : (Vertex11) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel11 newLabel11 a ∈ vertices12 := by decide
theorem labels11_cover : ∀ t : Vertex12, ∃ a : (Vertex11) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel11 newLabel11 a = t.val := by decide
def labels11 : ((Vertex11) ⊕ (Option (Bool × Bool))) ≃ Vertex12 :=
  sumLabels vertices12 oldLabel11 newLabel11 (Subtype.val_injective)
    newLabel11_injective fresh11 labels11_mem labels11_cover
theorem adjacency11 : ∀ x y : (Vertex11) ⊕ (Option (Bool × Bool)),
    graph12.Adj (labels11 x) (labels11 y) ↔ (crossingSuspension graph11 ends11).Adj x y := by decide
theorem mappedGraph11 : (crossingSuspension graph11 ends11).map labels11 = graph12 :=
  map_eq_of_forward (crossingSuspension graph11 ends11) graph12 labels11 adjacency11
def chain12 : MoveChain IndependenceComplexTorsionSeed.G0 graph12 12 := by
  simpa only [mappedGraph11] using (MoveChain.crossing chain11 ends11 edge11a edge11b labels11)

/- Certificate operation 12 (0-based): crossing_suspension. -/
def ends12 : (Bool × Bool) ↪ Vertex12 where
  toFun p := if p.1 then (if p.2 then ⟨26, by decide⟩ else ⟨3, by decide⟩)
    else (if p.2 then ⟨17, by decide⟩ else ⟨16, by decide⟩)
  inj' := by decide
theorem edge12a : graph12.Adj (ends12 (false, false)) (ends12 (false, true)) := by decide
theorem edge12b : graph12.Adj (ends12 (true, false)) (ends12 (true, true)) := by decide
def oldLabel12 : (Vertex12) → ℕ := fun x => x.val
def newLabel12 : Option (Bool × Bool) → ℕ := fun p => match p with
  | none => 51
  | some p => if p.1 then (if p.2 then 55 else 54)
      else (if p.2 then 53 else 52)
theorem newLabel12_injective : Function.Injective newLabel12 := by decide
theorem fresh12 : ∀ o : Vertex12, ∀ a : Option (Bool × Bool), oldLabel12 o ≠ newLabel12 a := by decide
theorem labels12_mem : ∀ a : (Vertex12) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel12 newLabel12 a ∈ vertices13 := by decide
theorem labels12_cover : ∀ t : Vertex13, ∃ a : (Vertex12) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel12 newLabel12 a = t.val := by decide
def labels12 : ((Vertex12) ⊕ (Option (Bool × Bool))) ≃ Vertex13 :=
  sumLabels vertices13 oldLabel12 newLabel12 (Subtype.val_injective)
    newLabel12_injective fresh12 labels12_mem labels12_cover
theorem adjacency12 : ∀ x y : (Vertex12) ⊕ (Option (Bool × Bool)),
    graph13.Adj (labels12 x) (labels12 y) ↔ (crossingSuspension graph12 ends12).Adj x y := by decide
theorem mappedGraph12 : (crossingSuspension graph12 ends12).map labels12 = graph13 :=
  map_eq_of_forward (crossingSuspension graph12 ends12) graph13 labels12 adjacency12
def chain13 : MoveChain IndependenceComplexTorsionSeed.G0 graph13 13 := by
  simpa only [mappedGraph12] using (MoveChain.crossing chain12 ends12 edge12a edge12b labels12)

/- Certificate operation 13 (0-based): crossing_suspension. -/
def ends13 : (Bool × Bool) ↪ Vertex13 where
  toFun p := if p.1 then (if p.2 then ⟨32, by decide⟩ else ⟨5, by decide⟩)
    else (if p.2 then ⟨29, by decide⟩ else ⟨4, by decide⟩)
  inj' := by decide
theorem edge13a : graph13.Adj (ends13 (false, false)) (ends13 (false, true)) := by decide
theorem edge13b : graph13.Adj (ends13 (true, false)) (ends13 (true, true)) := by decide
def oldLabel13 : (Vertex13) → ℕ := fun x => x.val
def newLabel13 : Option (Bool × Bool) → ℕ := fun p => match p with
  | none => 56
  | some p => if p.1 then (if p.2 then 60 else 59)
      else (if p.2 then 58 else 57)
theorem newLabel13_injective : Function.Injective newLabel13 := by decide
theorem fresh13 : ∀ o : Vertex13, ∀ a : Option (Bool × Bool), oldLabel13 o ≠ newLabel13 a := by decide
theorem labels13_mem : ∀ a : (Vertex13) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel13 newLabel13 a ∈ vertices14 := by decide
theorem labels13_cover : ∀ t : Vertex14, ∃ a : (Vertex13) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel13 newLabel13 a = t.val := by decide
def labels13 : ((Vertex13) ⊕ (Option (Bool × Bool))) ≃ Vertex14 :=
  sumLabels vertices14 oldLabel13 newLabel13 (Subtype.val_injective)
    newLabel13_injective fresh13 labels13_mem labels13_cover
theorem adjacency13 : ∀ x y : (Vertex13) ⊕ (Option (Bool × Bool)),
    graph14.Adj (labels13 x) (labels13 y) ↔ (crossingSuspension graph13 ends13).Adj x y := by decide
theorem mappedGraph13 : (crossingSuspension graph13 ends13).map labels13 = graph14 :=
  map_eq_of_forward (crossingSuspension graph13 ends13) graph14 labels13 adjacency13
def chain14 : MoveChain IndependenceComplexTorsionSeed.G0 graph14 14 := by
  simpa only [mappedGraph13] using (MoveChain.crossing chain13 ends13 edge13a edge13b labels13)

/- Certificate operation 14 (0-based): crossing_suspension. -/
def ends14 : (Bool × Bool) ↪ Vertex14 where
  toFun p := if p.1 then (if p.2 then ⟨38, by decide⟩ else ⟨7, by decide⟩)
    else (if p.2 then ⟨35, by decide⟩ else ⟨34, by decide⟩)
  inj' := by decide
theorem edge14a : graph14.Adj (ends14 (false, false)) (ends14 (false, true)) := by decide
theorem edge14b : graph14.Adj (ends14 (true, false)) (ends14 (true, true)) := by decide
def oldLabel14 : (Vertex14) → ℕ := fun x => x.val
def newLabel14 : Option (Bool × Bool) → ℕ := fun p => match p with
  | none => 61
  | some p => if p.1 then (if p.2 then 65 else 64)
      else (if p.2 then 63 else 62)
theorem newLabel14_injective : Function.Injective newLabel14 := by decide
theorem fresh14 : ∀ o : Vertex14, ∀ a : Option (Bool × Bool), oldLabel14 o ≠ newLabel14 a := by decide
theorem labels14_mem : ∀ a : (Vertex14) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel14 newLabel14 a ∈ vertices15 := by decide
theorem labels14_cover : ∀ t : Vertex15, ∃ a : (Vertex14) ⊕ (Option (Bool × Bool)),
    Sum.elim oldLabel14 newLabel14 a = t.val := by decide
def labels14 : ((Vertex14) ⊕ (Option (Bool × Bool))) ≃ Vertex15 :=
  sumLabels vertices15 oldLabel14 newLabel14 (Subtype.val_injective)
    newLabel14_injective fresh14 labels14_mem labels14_cover
theorem adjacency14 : ∀ x y : (Vertex14) ⊕ (Option (Bool × Bool)),
    graph15.Adj (labels14 x) (labels14 y) ↔ (crossingSuspension graph14 ends14).Adj x y := by decide
theorem mappedGraph14 : (crossingSuspension graph14 ends14).map labels14 = graph15 :=
  map_eq_of_forward (crossingSuspension graph14 ends14) graph15 labels14 adjacency14
def chain15 : MoveChain IndependenceComplexTorsionSeed.G0 graph15 15 := by
  simpa only [mappedGraph14] using (MoveChain.crossing chain14 ends14 edge14a edge14b labels14)

/- Certificate operation 15 (0-based): lozin_suspension. -/
def v15 : Vertex15 := ⟨0, by decide⟩
def Y15 : Finset Vertex15 := {⟨1, by decide⟩, ⟨47, by decide⟩}
def Z15 : Finset Vertex15 := {⟨48, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩}
theorem partition15 : ∀ x : Vertex15, graph15.Adj v15 x ↔ x ∈ Y15 ∨ x ∈ Z15 := by decide
theorem disjoint15 : Disjoint Y15 Z15 := by decide
theorem nonempty15 : Y15.Nonempty := by decide
def oldLabel15 : ({x : Vertex15 // x ≠ v15}) → ℕ := fun x => x.val.val
def newLabel15 : Fin 4 → ℕ := ![66, 67, 68, 69]
theorem newLabel15_injective : Function.Injective newLabel15 := by decide
theorem fresh15 : ∀ o : Vertex15, ∀ a : Fin 4, o.val ≠ newLabel15 a := by decide
theorem labels15_mem : ∀ a : ({x : Vertex15 // x ≠ v15}) ⊕ (Fin 4),
    Sum.elim oldLabel15 newLabel15 a ∈ vertices16 := by decide
theorem labels15_cover : ∀ t : Vertex16, ∃ a : ({x : Vertex15 // x ≠ v15}) ⊕ (Fin 4),
    Sum.elim oldLabel15 newLabel15 a = t.val := by decide
def labels15 : (({x : Vertex15 // x ≠ v15}) ⊕ (Fin 4)) ≃ Vertex16 :=
  sumLabels vertices16 oldLabel15 newLabel15 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel15_injective (fun o a => fresh15 o.val a) labels15_mem labels15_cover
theorem adjacency15 : ∀ x y : ({x : Vertex15 // x ≠ v15}) ⊕ (Fin 4),
    graph16.Adj (labels15 x) (labels15 y) ↔ (lozinSuspension graph15 v15 Y15 Z15).Adj x y := by decide
theorem mappedGraph15 : (lozinSuspension graph15 v15 Y15 Z15).map labels15 = graph16 :=
  map_eq_of_forward (lozinSuspension graph15 v15 Y15 Z15) graph16 labels15 adjacency15
def chain16 : MoveChain IndependenceComplexTorsionSeed.G0 graph16 16 := by
  simpa only [mappedGraph15] using (MoveChain.lozin chain15 v15 Y15 Z15 partition15 disjoint15 nonempty15 labels15)

/- Certificate operation 16 (0-based): lozin_suspension. -/
def v16 : Vertex16 := ⟨1, by decide⟩
def Y16 : Finset Vertex16 := {⟨2, by decide⟩, ⟨66, by decide⟩}
def Z16 : Finset Vertex16 := {⟨47, by decide⟩, ⟨49, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩}
theorem partition16 : ∀ x : Vertex16, graph16.Adj v16 x ↔ x ∈ Y16 ∨ x ∈ Z16 := by decide
theorem disjoint16 : Disjoint Y16 Z16 := by decide
theorem nonempty16 : Y16.Nonempty := by decide
def oldLabel16 : ({x : Vertex16 // x ≠ v16}) → ℕ := fun x => x.val.val
def newLabel16 : Fin 4 → ℕ := ![70, 71, 72, 73]
theorem newLabel16_injective : Function.Injective newLabel16 := by decide
theorem fresh16 : ∀ o : Vertex16, ∀ a : Fin 4, o.val ≠ newLabel16 a := by decide
theorem labels16_mem : ∀ a : ({x : Vertex16 // x ≠ v16}) ⊕ (Fin 4),
    Sum.elim oldLabel16 newLabel16 a ∈ vertices17 := by decide
theorem labels16_cover : ∀ t : Vertex17, ∃ a : ({x : Vertex16 // x ≠ v16}) ⊕ (Fin 4),
    Sum.elim oldLabel16 newLabel16 a = t.val := by decide
def labels16 : (({x : Vertex16 // x ≠ v16}) ⊕ (Fin 4)) ≃ Vertex17 :=
  sumLabels vertices17 oldLabel16 newLabel16 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel16_injective (fun o a => fresh16 o.val a) labels16_mem labels16_cover
theorem adjacency16 : ∀ x y : ({x : Vertex16 // x ≠ v16}) ⊕ (Fin 4),
    graph17.Adj (labels16 x) (labels16 y) ↔ (lozinSuspension graph16 v16 Y16 Z16).Adj x y := by decide
theorem mappedGraph16 : (lozinSuspension graph16 v16 Y16 Z16).map labels16 = graph17 :=
  map_eq_of_forward (lozinSuspension graph16 v16 Y16 Z16) graph17 labels16 adjacency16
def chain17 : MoveChain IndependenceComplexTorsionSeed.G0 graph17 17 := by
  simpa only [mappedGraph16] using (MoveChain.lozin chain16 v16 Y16 Z16 partition16 disjoint16 nonempty16 labels16)

/- Certificate operation 17 (0-based): lozin_suspension. -/
def v17 : Vertex17 := ⟨2, by decide⟩
def Y17 : Finset Vertex17 := {⟨3, by decide⟩, ⟨70, by decide⟩}
def Z17 : Finset Vertex17 := {⟨69, by decide⟩, ⟨9, by decide⟩}
theorem partition17 : ∀ x : Vertex17, graph17.Adj v17 x ↔ x ∈ Y17 ∨ x ∈ Z17 := by decide
theorem disjoint17 : Disjoint Y17 Z17 := by decide
theorem nonempty17 : Y17.Nonempty := by decide
def oldLabel17 : ({x : Vertex17 // x ≠ v17}) → ℕ := fun x => x.val.val
def newLabel17 : Fin 4 → ℕ := ![74, 75, 76, 77]
theorem newLabel17_injective : Function.Injective newLabel17 := by decide
theorem fresh17 : ∀ o : Vertex17, ∀ a : Fin 4, o.val ≠ newLabel17 a := by decide
theorem labels17_mem : ∀ a : ({x : Vertex17 // x ≠ v17}) ⊕ (Fin 4),
    Sum.elim oldLabel17 newLabel17 a ∈ vertices18 := by decide
theorem labels17_cover : ∀ t : Vertex18, ∃ a : ({x : Vertex17 // x ≠ v17}) ⊕ (Fin 4),
    Sum.elim oldLabel17 newLabel17 a = t.val := by decide
def labels17 : (({x : Vertex17 // x ≠ v17}) ⊕ (Fin 4)) ≃ Vertex18 :=
  sumLabels vertices18 oldLabel17 newLabel17 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel17_injective (fun o a => fresh17 o.val a) labels17_mem labels17_cover
theorem adjacency17 : ∀ x y : ({x : Vertex17 // x ≠ v17}) ⊕ (Fin 4),
    graph18.Adj (labels17 x) (labels17 y) ↔ (lozinSuspension graph17 v17 Y17 Z17).Adj x y := by decide
theorem mappedGraph17 : (lozinSuspension graph17 v17 Y17 Z17).map labels17 = graph18 :=
  map_eq_of_forward (lozinSuspension graph17 v17 Y17 Z17) graph18 labels17 adjacency17
def chain18 : MoveChain IndependenceComplexTorsionSeed.G0 graph18 18 := by
  simpa only [mappedGraph17] using (MoveChain.lozin chain17 v17 Y17 Z17 partition17 disjoint17 nonempty17 labels17)

/- Certificate operation 18 (0-based): lozin_suspension. -/
def v18 : Vertex18 := ⟨3, by decide⟩
def Y18 : Finset Vertex18 := {⟨5, by decide⟩, ⟨9, by decide⟩}
def Z18 : Finset Vertex18 := {⟨74, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩}
theorem partition18 : ∀ x : Vertex18, graph18.Adj v18 x ↔ x ∈ Y18 ∨ x ∈ Z18 := by decide
theorem disjoint18 : Disjoint Y18 Z18 := by decide
theorem nonempty18 : Y18.Nonempty := by decide
def oldLabel18 : ({x : Vertex18 // x ≠ v18}) → ℕ := fun x => x.val.val
def newLabel18 : Fin 4 → ℕ := ![78, 79, 80, 81]
theorem newLabel18_injective : Function.Injective newLabel18 := by decide
theorem fresh18 : ∀ o : Vertex18, ∀ a : Fin 4, o.val ≠ newLabel18 a := by decide
theorem labels18_mem : ∀ a : ({x : Vertex18 // x ≠ v18}) ⊕ (Fin 4),
    Sum.elim oldLabel18 newLabel18 a ∈ vertices19 := by decide
theorem labels18_cover : ∀ t : Vertex19, ∃ a : ({x : Vertex18 // x ≠ v18}) ⊕ (Fin 4),
    Sum.elim oldLabel18 newLabel18 a = t.val := by decide
def labels18 : (({x : Vertex18 // x ≠ v18}) ⊕ (Fin 4)) ≃ Vertex19 :=
  sumLabels vertices19 oldLabel18 newLabel18 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel18_injective (fun o a => fresh18 o.val a) labels18_mem labels18_cover
theorem adjacency18 : ∀ x y : ({x : Vertex18 // x ≠ v18}) ⊕ (Fin 4),
    graph19.Adj (labels18 x) (labels18 y) ↔ (lozinSuspension graph18 v18 Y18 Z18).Adj x y := by decide
theorem mappedGraph18 : (lozinSuspension graph18 v18 Y18 Z18).map labels18 = graph19 :=
  map_eq_of_forward (lozinSuspension graph18 v18 Y18 Z18) graph19 labels18 adjacency18
def chain19 : MoveChain IndependenceComplexTorsionSeed.G0 graph19 19 := by
  simpa only [mappedGraph18] using (MoveChain.lozin chain18 v18 Y18 Z18 partition18 disjoint18 nonempty18 labels18)

/- Certificate operation 19 (0-based): lozin_suspension. -/
def v19 : Vertex19 := ⟨4, by decide⟩
def Y19 : Finset Vertex19 := {⟨5, by decide⟩, ⟨57, by decide⟩}
def Z19 : Finset Vertex19 := {⟨58, by decide⟩, ⟨7, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩}
theorem partition19 : ∀ x : Vertex19, graph19.Adj v19 x ↔ x ∈ Y19 ∨ x ∈ Z19 := by decide
theorem disjoint19 : Disjoint Y19 Z19 := by decide
theorem nonempty19 : Y19.Nonempty := by decide
def oldLabel19 : ({x : Vertex19 // x ≠ v19}) → ℕ := fun x => x.val.val
def newLabel19 : Fin 4 → ℕ := ![82, 83, 84, 85]
theorem newLabel19_injective : Function.Injective newLabel19 := by decide
theorem fresh19 : ∀ o : Vertex19, ∀ a : Fin 4, o.val ≠ newLabel19 a := by decide
theorem labels19_mem : ∀ a : ({x : Vertex19 // x ≠ v19}) ⊕ (Fin 4),
    Sum.elim oldLabel19 newLabel19 a ∈ vertices20 := by decide
theorem labels19_cover : ∀ t : Vertex20, ∃ a : ({x : Vertex19 // x ≠ v19}) ⊕ (Fin 4),
    Sum.elim oldLabel19 newLabel19 a = t.val := by decide
def labels19 : (({x : Vertex19 // x ≠ v19}) ⊕ (Fin 4)) ≃ Vertex20 :=
  sumLabels vertices20 oldLabel19 newLabel19 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel19_injective (fun o a => fresh19 o.val a) labels19_mem labels19_cover
theorem adjacency19 : ∀ x y : ({x : Vertex19 // x ≠ v19}) ⊕ (Fin 4),
    graph20.Adj (labels19 x) (labels19 y) ↔ (lozinSuspension graph19 v19 Y19 Z19).Adj x y := by decide
theorem mappedGraph19 : (lozinSuspension graph19 v19 Y19 Z19).map labels19 = graph20 :=
  map_eq_of_forward (lozinSuspension graph19 v19 Y19 Z19) graph20 labels19 adjacency19
def chain20 : MoveChain IndependenceComplexTorsionSeed.G0 graph20 20 := by
  simpa only [mappedGraph19] using (MoveChain.lozin chain19 v19 Y19 Z19 partition19 disjoint19 nonempty19 labels19)

/- Certificate operation 20 (0-based): lozin_suspension. -/
def v20 : Vertex20 := ⟨5, by decide⟩
def Y20 : Finset Vertex20 := {⟨10, by decide⟩, ⟨78, by decide⟩}
def Z20 : Finset Vertex20 := {⟨19, by decide⟩, ⟨82, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩}
theorem partition20 : ∀ x : Vertex20, graph20.Adj v20 x ↔ x ∈ Y20 ∨ x ∈ Z20 := by decide
theorem disjoint20 : Disjoint Y20 Z20 := by decide
theorem nonempty20 : Y20.Nonempty := by decide
def oldLabel20 : ({x : Vertex20 // x ≠ v20}) → ℕ := fun x => x.val.val
def newLabel20 : Fin 4 → ℕ := ![86, 87, 88, 89]
theorem newLabel20_injective : Function.Injective newLabel20 := by decide
theorem fresh20 : ∀ o : Vertex20, ∀ a : Fin 4, o.val ≠ newLabel20 a := by decide
theorem labels20_mem : ∀ a : ({x : Vertex20 // x ≠ v20}) ⊕ (Fin 4),
    Sum.elim oldLabel20 newLabel20 a ∈ vertices21 := by decide
theorem labels20_cover : ∀ t : Vertex21, ∃ a : ({x : Vertex20 // x ≠ v20}) ⊕ (Fin 4),
    Sum.elim oldLabel20 newLabel20 a = t.val := by decide
def labels20 : (({x : Vertex20 // x ≠ v20}) ⊕ (Fin 4)) ≃ Vertex21 :=
  sumLabels vertices21 oldLabel20 newLabel20 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel20_injective (fun o a => fresh20 o.val a) labels20_mem labels20_cover
theorem adjacency20 : ∀ x y : ({x : Vertex20 // x ≠ v20}) ⊕ (Fin 4),
    graph21.Adj (labels20 x) (labels20 y) ↔ (lozinSuspension graph20 v20 Y20 Z20).Adj x y := by decide
theorem mappedGraph20 : (lozinSuspension graph20 v20 Y20 Z20).map labels20 = graph21 :=
  map_eq_of_forward (lozinSuspension graph20 v20 Y20 Z20) graph21 labels20 adjacency20
def chain21 : MoveChain IndependenceComplexTorsionSeed.G0 graph21 21 := by
  simpa only [mappedGraph20] using (MoveChain.lozin chain20 v20 Y20 Z20 partition20 disjoint20 nonempty20 labels20)

/- Certificate operation 21 (0-based): lozin_suspension. -/
def v21 : Vertex21 := ⟨6, by decide⟩
def Y21 : Finset Vertex21 := {⟨7, by decide⟩, ⟨69, by decide⟩}
def Z21 : Finset Vertex21 := {⟨8, by decide⟩, ⟨37, by decide⟩}
theorem partition21 : ∀ x : Vertex21, graph21.Adj v21 x ↔ x ∈ Y21 ∨ x ∈ Z21 := by decide
theorem disjoint21 : Disjoint Y21 Z21 := by decide
theorem nonempty21 : Y21.Nonempty := by decide
def oldLabel21 : ({x : Vertex21 // x ≠ v21}) → ℕ := fun x => x.val.val
def newLabel21 : Fin 4 → ℕ := ![90, 91, 92, 93]
theorem newLabel21_injective : Function.Injective newLabel21 := by decide
theorem fresh21 : ∀ o : Vertex21, ∀ a : Fin 4, o.val ≠ newLabel21 a := by decide
theorem labels21_mem : ∀ a : ({x : Vertex21 // x ≠ v21}) ⊕ (Fin 4),
    Sum.elim oldLabel21 newLabel21 a ∈ vertices22 := by decide
theorem labels21_cover : ∀ t : Vertex22, ∃ a : ({x : Vertex21 // x ≠ v21}) ⊕ (Fin 4),
    Sum.elim oldLabel21 newLabel21 a = t.val := by decide
def labels21 : (({x : Vertex21 // x ≠ v21}) ⊕ (Fin 4)) ≃ Vertex22 :=
  sumLabels vertices22 oldLabel21 newLabel21 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel21_injective (fun o a => fresh21 o.val a) labels21_mem labels21_cover
theorem adjacency21 : ∀ x y : ({x : Vertex21 // x ≠ v21}) ⊕ (Fin 4),
    graph22.Adj (labels21 x) (labels21 y) ↔ (lozinSuspension graph21 v21 Y21 Z21).Adj x y := by decide
theorem mappedGraph21 : (lozinSuspension graph21 v21 Y21 Z21).map labels21 = graph22 :=
  map_eq_of_forward (lozinSuspension graph21 v21 Y21 Z21) graph22 labels21 adjacency21
def chain22 : MoveChain IndependenceComplexTorsionSeed.G0 graph22 22 := by
  simpa only [mappedGraph21] using (MoveChain.lozin chain21 v21 Y21 Z21 partition21 disjoint21 nonempty21 labels21)

/- Certificate operation 22 (0-based): lozin_suspension. -/
def v22 : Vertex22 := ⟨7, by decide⟩
def Y22 : Finset Vertex22 := {⟨25, by decide⟩, ⟨90, by decide⟩}
def Z22 : Finset Vertex22 := {⟨64, by decide⟩, ⟨62, by decide⟩, ⟨85, by decide⟩}
theorem partition22 : ∀ x : Vertex22, graph22.Adj v22 x ↔ x ∈ Y22 ∨ x ∈ Z22 := by decide
theorem disjoint22 : Disjoint Y22 Z22 := by decide
theorem nonempty22 : Y22.Nonempty := by decide
def oldLabel22 : ({x : Vertex22 // x ≠ v22}) → ℕ := fun x => x.val.val
def newLabel22 : Fin 4 → ℕ := ![94, 95, 96, 97]
theorem newLabel22_injective : Function.Injective newLabel22 := by decide
theorem fresh22 : ∀ o : Vertex22, ∀ a : Fin 4, o.val ≠ newLabel22 a := by decide
theorem labels22_mem : ∀ a : ({x : Vertex22 // x ≠ v22}) ⊕ (Fin 4),
    Sum.elim oldLabel22 newLabel22 a ∈ vertices23 := by decide
theorem labels22_cover : ∀ t : Vertex23, ∃ a : ({x : Vertex22 // x ≠ v22}) ⊕ (Fin 4),
    Sum.elim oldLabel22 newLabel22 a = t.val := by decide
def labels22 : (({x : Vertex22 // x ≠ v22}) ⊕ (Fin 4)) ≃ Vertex23 :=
  sumLabels vertices23 oldLabel22 newLabel22 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel22_injective (fun o a => fresh22 o.val a) labels22_mem labels22_cover
theorem adjacency22 : ∀ x y : ({x : Vertex22 // x ≠ v22}) ⊕ (Fin 4),
    graph23.Adj (labels22 x) (labels22 y) ↔ (lozinSuspension graph22 v22 Y22 Z22).Adj x y := by decide
theorem mappedGraph22 : (lozinSuspension graph22 v22 Y22 Z22).map labels22 = graph23 :=
  map_eq_of_forward (lozinSuspension graph22 v22 Y22 Z22) graph23 labels22 adjacency22
def chain23 : MoveChain IndependenceComplexTorsionSeed.G0 graph23 23 := by
  simpa only [mappedGraph22] using (MoveChain.lozin chain22 v22 Y22 Z22 partition22 disjoint22 nonempty22 labels22)

/- Certificate operation 23 (0-based): lozin_suspension. -/
def v23 : Vertex23 := ⟨8, by decide⟩
def Y23 : Finset Vertex23 := {⟨9, by decide⟩, ⟨93, by decide⟩}
def Z23 : Finset Vertex23 := {⟨40, by decide⟩, ⟨10, by decide⟩}
theorem partition23 : ∀ x : Vertex23, graph23.Adj v23 x ↔ x ∈ Y23 ∨ x ∈ Z23 := by decide
theorem disjoint23 : Disjoint Y23 Z23 := by decide
theorem nonempty23 : Y23.Nonempty := by decide
def oldLabel23 : ({x : Vertex23 // x ≠ v23}) → ℕ := fun x => x.val.val
def newLabel23 : Fin 4 → ℕ := ![98, 99, 100, 101]
theorem newLabel23_injective : Function.Injective newLabel23 := by decide
theorem fresh23 : ∀ o : Vertex23, ∀ a : Fin 4, o.val ≠ newLabel23 a := by decide
theorem labels23_mem : ∀ a : ({x : Vertex23 // x ≠ v23}) ⊕ (Fin 4),
    Sum.elim oldLabel23 newLabel23 a ∈ vertices24 := by decide
theorem labels23_cover : ∀ t : Vertex24, ∃ a : ({x : Vertex23 // x ≠ v23}) ⊕ (Fin 4),
    Sum.elim oldLabel23 newLabel23 a = t.val := by decide
def labels23 : (({x : Vertex23 // x ≠ v23}) ⊕ (Fin 4)) ≃ Vertex24 :=
  sumLabels vertices24 oldLabel23 newLabel23 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel23_injective (fun o a => fresh23 o.val a) labels23_mem labels23_cover
theorem adjacency23 : ∀ x y : ({x : Vertex23 // x ≠ v23}) ⊕ (Fin 4),
    graph24.Adj (labels23 x) (labels23 y) ↔ (lozinSuspension graph23 v23 Y23 Z23).Adj x y := by decide
theorem mappedGraph23 : (lozinSuspension graph23 v23 Y23 Z23).map labels23 = graph24 :=
  map_eq_of_forward (lozinSuspension graph23 v23 Y23 Z23) graph24 labels23 adjacency23
def chain24 : MoveChain IndependenceComplexTorsionSeed.G0 graph24 24 := by
  simpa only [mappedGraph23] using (MoveChain.lozin chain23 v23 Y23 Z23 partition23 disjoint23 nonempty23 labels23)

/- Certificate operation 24 (0-based): lozin_suspension. -/
def v24 : Vertex24 := ⟨9, by decide⟩
def Y24 : Finset Vertex24 := {⟨10, by decide⟩, ⟨78, by decide⟩}
def Z24 : Finset Vertex24 := {⟨77, by decide⟩, ⟨98, by decide⟩}
theorem partition24 : ∀ x : Vertex24, graph24.Adj v24 x ↔ x ∈ Y24 ∨ x ∈ Z24 := by decide
theorem disjoint24 : Disjoint Y24 Z24 := by decide
theorem nonempty24 : Y24.Nonempty := by decide
def oldLabel24 : ({x : Vertex24 // x ≠ v24}) → ℕ := fun x => x.val.val
def newLabel24 : Fin 4 → ℕ := ![102, 103, 104, 105]
theorem newLabel24_injective : Function.Injective newLabel24 := by decide
theorem fresh24 : ∀ o : Vertex24, ∀ a : Fin 4, o.val ≠ newLabel24 a := by decide
theorem labels24_mem : ∀ a : ({x : Vertex24 // x ≠ v24}) ⊕ (Fin 4),
    Sum.elim oldLabel24 newLabel24 a ∈ vertices25 := by decide
theorem labels24_cover : ∀ t : Vertex25, ∃ a : ({x : Vertex24 // x ≠ v24}) ⊕ (Fin 4),
    Sum.elim oldLabel24 newLabel24 a = t.val := by decide
def labels24 : (({x : Vertex24 // x ≠ v24}) ⊕ (Fin 4)) ≃ Vertex25 :=
  sumLabels vertices25 oldLabel24 newLabel24 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel24_injective (fun o a => fresh24 o.val a) labels24_mem labels24_cover
theorem adjacency24 : ∀ x y : ({x : Vertex24 // x ≠ v24}) ⊕ (Fin 4),
    graph25.Adj (labels24 x) (labels24 y) ↔ (lozinSuspension graph24 v24 Y24 Z24).Adj x y := by decide
theorem mappedGraph24 : (lozinSuspension graph24 v24 Y24 Z24).map labels24 = graph25 :=
  map_eq_of_forward (lozinSuspension graph24 v24 Y24 Z24) graph25 labels24 adjacency24
def chain25 : MoveChain IndependenceComplexTorsionSeed.G0 graph25 25 := by
  simpa only [mappedGraph24] using (MoveChain.lozin chain24 v24 Y24 Z24 partition24 disjoint24 nonempty24 labels24)

/- Certificate operation 25 (0-based): lozin_suspension. -/
def v25 : Vertex25 := ⟨10, by decide⟩
def Y25 : Finset Vertex25 := {⟨31, by decide⟩, ⟨101, by decide⟩}
def Z25 : Finset Vertex25 := {⟨102, by decide⟩, ⟨86, by decide⟩}
theorem partition25 : ∀ x : Vertex25, graph25.Adj v25 x ↔ x ∈ Y25 ∨ x ∈ Z25 := by decide
theorem disjoint25 : Disjoint Y25 Z25 := by decide
theorem nonempty25 : Y25.Nonempty := by decide
def oldLabel25 : ({x : Vertex25 // x ≠ v25}) → ℕ := fun x => x.val.val
def newLabel25 : Fin 4 → ℕ := ![106, 107, 108, 109]
theorem newLabel25_injective : Function.Injective newLabel25 := by decide
theorem fresh25 : ∀ o : Vertex25, ∀ a : Fin 4, o.val ≠ newLabel25 a := by decide
theorem labels25_mem : ∀ a : ({x : Vertex25 // x ≠ v25}) ⊕ (Fin 4),
    Sum.elim oldLabel25 newLabel25 a ∈ vertices26 := by decide
theorem labels25_cover : ∀ t : Vertex26, ∃ a : ({x : Vertex25 // x ≠ v25}) ⊕ (Fin 4),
    Sum.elim oldLabel25 newLabel25 a = t.val := by decide
def labels25 : (({x : Vertex25 // x ≠ v25}) ⊕ (Fin 4)) ≃ Vertex26 :=
  sumLabels vertices26 oldLabel25 newLabel25 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel25_injective (fun o a => fresh25 o.val a) labels25_mem labels25_cover
theorem adjacency25 : ∀ x y : ({x : Vertex25 // x ≠ v25}) ⊕ (Fin 4),
    graph26.Adj (labels25 x) (labels25 y) ↔ (lozinSuspension graph25 v25 Y25 Z25).Adj x y := by decide
theorem mappedGraph25 : (lozinSuspension graph25 v25 Y25 Z25).map labels25 = graph26 :=
  map_eq_of_forward (lozinSuspension graph25 v25 Y25 Z25) graph26 labels25 adjacency25
def chain26 : MoveChain IndependenceComplexTorsionSeed.G0 graph26 26 := by
  simpa only [mappedGraph25] using (MoveChain.lozin chain25 v25 Y25 Z25 partition25 disjoint25 nonempty25 labels25)

/- Certificate operation 26 (0-based): lozin_suspension. -/
def v26 : Vertex26 := ⟨41, by decide⟩
def Y26 : Finset Vertex26 := {⟨42, by decide⟩, ⟨44, by decide⟩}
def Z26 : Finset Vertex26 := {⟨45, by decide⟩, ⟨43, by decide⟩}
theorem partition26 : ∀ x : Vertex26, graph26.Adj v26 x ↔ x ∈ Y26 ∨ x ∈ Z26 := by decide
theorem disjoint26 : Disjoint Y26 Z26 := by decide
theorem nonempty26 : Y26.Nonempty := by decide
def oldLabel26 : ({x : Vertex26 // x ≠ v26}) → ℕ := fun x => x.val.val
def newLabel26 : Fin 4 → ℕ := ![110, 111, 112, 113]
theorem newLabel26_injective : Function.Injective newLabel26 := by decide
theorem fresh26 : ∀ o : Vertex26, ∀ a : Fin 4, o.val ≠ newLabel26 a := by decide
theorem labels26_mem : ∀ a : ({x : Vertex26 // x ≠ v26}) ⊕ (Fin 4),
    Sum.elim oldLabel26 newLabel26 a ∈ vertices27 := by decide
theorem labels26_cover : ∀ t : Vertex27, ∃ a : ({x : Vertex26 // x ≠ v26}) ⊕ (Fin 4),
    Sum.elim oldLabel26 newLabel26 a = t.val := by decide
def labels26 : (({x : Vertex26 // x ≠ v26}) ⊕ (Fin 4)) ≃ Vertex27 :=
  sumLabels vertices27 oldLabel26 newLabel26 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel26_injective (fun o a => fresh26 o.val a) labels26_mem labels26_cover
theorem adjacency26 : ∀ x y : ({x : Vertex26 // x ≠ v26}) ⊕ (Fin 4),
    graph27.Adj (labels26 x) (labels26 y) ↔ (lozinSuspension graph26 v26 Y26 Z26).Adj x y := by decide
theorem mappedGraph26 : (lozinSuspension graph26 v26 Y26 Z26).map labels26 = graph27 :=
  map_eq_of_forward (lozinSuspension graph26 v26 Y26 Z26) graph27 labels26 adjacency26
def chain27 : MoveChain IndependenceComplexTorsionSeed.G0 graph27 27 := by
  simpa only [mappedGraph26] using (MoveChain.lozin chain26 v26 Y26 Z26 partition26 disjoint26 nonempty26 labels26)

/- Certificate operation 27 (0-based): lozin_suspension. -/
def v27 : Vertex27 := ⟨46, by decide⟩
def Y27 : Finset Vertex27 := {⟨48, by decide⟩, ⟨47, by decide⟩}
def Z27 : Finset Vertex27 := {⟨49, by decide⟩, ⟨50, by decide⟩}
theorem partition27 : ∀ x : Vertex27, graph27.Adj v27 x ↔ x ∈ Y27 ∨ x ∈ Z27 := by decide
theorem disjoint27 : Disjoint Y27 Z27 := by decide
theorem nonempty27 : Y27.Nonempty := by decide
def oldLabel27 : ({x : Vertex27 // x ≠ v27}) → ℕ := fun x => x.val.val
def newLabel27 : Fin 4 → ℕ := ![114, 115, 116, 117]
theorem newLabel27_injective : Function.Injective newLabel27 := by decide
theorem fresh27 : ∀ o : Vertex27, ∀ a : Fin 4, o.val ≠ newLabel27 a := by decide
theorem labels27_mem : ∀ a : ({x : Vertex27 // x ≠ v27}) ⊕ (Fin 4),
    Sum.elim oldLabel27 newLabel27 a ∈ vertices28 := by decide
theorem labels27_cover : ∀ t : Vertex28, ∃ a : ({x : Vertex27 // x ≠ v27}) ⊕ (Fin 4),
    Sum.elim oldLabel27 newLabel27 a = t.val := by decide
def labels27 : (({x : Vertex27 // x ≠ v27}) ⊕ (Fin 4)) ≃ Vertex28 :=
  sumLabels vertices28 oldLabel27 newLabel27 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel27_injective (fun o a => fresh27 o.val a) labels27_mem labels27_cover
theorem adjacency27 : ∀ x y : ({x : Vertex27 // x ≠ v27}) ⊕ (Fin 4),
    graph28.Adj (labels27 x) (labels27 y) ↔ (lozinSuspension graph27 v27 Y27 Z27).Adj x y := by decide
theorem mappedGraph27 : (lozinSuspension graph27 v27 Y27 Z27).map labels27 = graph28 :=
  map_eq_of_forward (lozinSuspension graph27 v27 Y27 Z27) graph28 labels27 adjacency27
def chain28 : MoveChain IndependenceComplexTorsionSeed.G0 graph28 28 := by
  simpa only [mappedGraph27] using (MoveChain.lozin chain27 v27 Y27 Z27 partition27 disjoint27 nonempty27 labels27)

/- Certificate operation 28 (0-based): lozin_suspension. -/
def v28 : Vertex28 := ⟨51, by decide⟩
def Y28 : Finset Vertex28 := {⟨52, by decide⟩, ⟨54, by decide⟩}
def Z28 : Finset Vertex28 := {⟨55, by decide⟩, ⟨53, by decide⟩}
theorem partition28 : ∀ x : Vertex28, graph28.Adj v28 x ↔ x ∈ Y28 ∨ x ∈ Z28 := by decide
theorem disjoint28 : Disjoint Y28 Z28 := by decide
theorem nonempty28 : Y28.Nonempty := by decide
def oldLabel28 : ({x : Vertex28 // x ≠ v28}) → ℕ := fun x => x.val.val
def newLabel28 : Fin 4 → ℕ := ![118, 119, 120, 121]
theorem newLabel28_injective : Function.Injective newLabel28 := by decide
theorem fresh28 : ∀ o : Vertex28, ∀ a : Fin 4, o.val ≠ newLabel28 a := by decide
theorem labels28_mem : ∀ a : ({x : Vertex28 // x ≠ v28}) ⊕ (Fin 4),
    Sum.elim oldLabel28 newLabel28 a ∈ vertices29 := by decide
theorem labels28_cover : ∀ t : Vertex29, ∃ a : ({x : Vertex28 // x ≠ v28}) ⊕ (Fin 4),
    Sum.elim oldLabel28 newLabel28 a = t.val := by decide
def labels28 : (({x : Vertex28 // x ≠ v28}) ⊕ (Fin 4)) ≃ Vertex29 :=
  sumLabels vertices29 oldLabel28 newLabel28 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel28_injective (fun o a => fresh28 o.val a) labels28_mem labels28_cover
theorem adjacency28 : ∀ x y : ({x : Vertex28 // x ≠ v28}) ⊕ (Fin 4),
    graph29.Adj (labels28 x) (labels28 y) ↔ (lozinSuspension graph28 v28 Y28 Z28).Adj x y := by decide
theorem mappedGraph28 : (lozinSuspension graph28 v28 Y28 Z28).map labels28 = graph29 :=
  map_eq_of_forward (lozinSuspension graph28 v28 Y28 Z28) graph29 labels28 adjacency28
def chain29 : MoveChain IndependenceComplexTorsionSeed.G0 graph29 29 := by
  simpa only [mappedGraph28] using (MoveChain.lozin chain28 v28 Y28 Z28 partition28 disjoint28 nonempty28 labels28)

/- Certificate operation 29 (0-based): lozin_suspension. -/
def v29 : Vertex29 := ⟨56, by decide⟩
def Y29 : Finset Vertex29 := {⟨57, by decide⟩, ⟨58, by decide⟩}
def Z29 : Finset Vertex29 := {⟨60, by decide⟩, ⟨59, by decide⟩}
theorem partition29 : ∀ x : Vertex29, graph29.Adj v29 x ↔ x ∈ Y29 ∨ x ∈ Z29 := by decide
theorem disjoint29 : Disjoint Y29 Z29 := by decide
theorem nonempty29 : Y29.Nonempty := by decide
def oldLabel29 : ({x : Vertex29 // x ≠ v29}) → ℕ := fun x => x.val.val
def newLabel29 : Fin 4 → ℕ := ![122, 123, 124, 125]
theorem newLabel29_injective : Function.Injective newLabel29 := by decide
theorem fresh29 : ∀ o : Vertex29, ∀ a : Fin 4, o.val ≠ newLabel29 a := by decide
theorem labels29_mem : ∀ a : ({x : Vertex29 // x ≠ v29}) ⊕ (Fin 4),
    Sum.elim oldLabel29 newLabel29 a ∈ vertices30 := by decide
theorem labels29_cover : ∀ t : Vertex30, ∃ a : ({x : Vertex29 // x ≠ v29}) ⊕ (Fin 4),
    Sum.elim oldLabel29 newLabel29 a = t.val := by decide
def labels29 : (({x : Vertex29 // x ≠ v29}) ⊕ (Fin 4)) ≃ Vertex30 :=
  sumLabels vertices30 oldLabel29 newLabel29 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel29_injective (fun o a => fresh29 o.val a) labels29_mem labels29_cover
theorem adjacency29 : ∀ x y : ({x : Vertex29 // x ≠ v29}) ⊕ (Fin 4),
    graph30.Adj (labels29 x) (labels29 y) ↔ (lozinSuspension graph29 v29 Y29 Z29).Adj x y := by decide
theorem mappedGraph29 : (lozinSuspension graph29 v29 Y29 Z29).map labels29 = graph30 :=
  map_eq_of_forward (lozinSuspension graph29 v29 Y29 Z29) graph30 labels29 adjacency29
def chain30 : MoveChain IndependenceComplexTorsionSeed.G0 graph30 30 := by
  simpa only [mappedGraph29] using (MoveChain.lozin chain29 v29 Y29 Z29 partition29 disjoint29 nonempty29 labels29)

/- Certificate operation 30 (0-based): lozin_suspension. -/
def v30 : Vertex30 := ⟨61, by decide⟩
def Y30 : Finset Vertex30 := {⟨62, by decide⟩, ⟨63, by decide⟩}
def Z30 : Finset Vertex30 := {⟨65, by decide⟩, ⟨64, by decide⟩}
theorem partition30 : ∀ x : Vertex30, graph30.Adj v30 x ↔ x ∈ Y30 ∨ x ∈ Z30 := by decide
theorem disjoint30 : Disjoint Y30 Z30 := by decide
theorem nonempty30 : Y30.Nonempty := by decide
def oldLabel30 : ({x : Vertex30 // x ≠ v30}) → ℕ := fun x => x.val.val
def newLabel30 : Fin 4 → ℕ := ![126, 127, 128, 129]
theorem newLabel30_injective : Function.Injective newLabel30 := by decide
theorem fresh30 : ∀ o : Vertex30, ∀ a : Fin 4, o.val ≠ newLabel30 a := by decide
theorem labels30_mem : ∀ a : ({x : Vertex30 // x ≠ v30}) ⊕ (Fin 4),
    Sum.elim oldLabel30 newLabel30 a ∈ vertices31 := by decide
theorem labels30_cover : ∀ t : Vertex31, ∃ a : ({x : Vertex30 // x ≠ v30}) ⊕ (Fin 4),
    Sum.elim oldLabel30 newLabel30 a = t.val := by decide
def labels30 : (({x : Vertex30 // x ≠ v30}) ⊕ (Fin 4)) ≃ Vertex31 :=
  sumLabels vertices31 oldLabel30 newLabel30 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel30_injective (fun o a => fresh30 o.val a) labels30_mem labels30_cover
theorem adjacency30 : ∀ x y : ({x : Vertex30 // x ≠ v30}) ⊕ (Fin 4),
    graph31.Adj (labels30 x) (labels30 y) ↔ (lozinSuspension graph30 v30 Y30 Z30).Adj x y := by decide
theorem mappedGraph30 : (lozinSuspension graph30 v30 Y30 Z30).map labels30 = graph31 :=
  map_eq_of_forward (lozinSuspension graph30 v30 Y30 Z30) graph31 labels30 adjacency30
def chain31 : MoveChain IndependenceComplexTorsionSeed.G0 graph31 31 := by
  simpa only [mappedGraph30] using (MoveChain.lozin chain30 v30 Y30 Z30 partition30 disjoint30 nonempty30 labels30)

/- Certificate operation 31 (0-based): lozin_suspension. -/
def v31 : Vertex31 := ⟨69, by decide⟩
def Y31 : Finset Vertex31 := {⟨90, by decide⟩, ⟨77, by decide⟩}
def Z31 : Finset Vertex31 := {⟨68, by decide⟩, ⟨48, by decide⟩}
theorem partition31 : ∀ x : Vertex31, graph31.Adj v31 x ↔ x ∈ Y31 ∨ x ∈ Z31 := by decide
theorem disjoint31 : Disjoint Y31 Z31 := by decide
theorem nonempty31 : Y31.Nonempty := by decide
def oldLabel31 : ({x : Vertex31 // x ≠ v31}) → ℕ := fun x => x.val.val
def newLabel31 : Fin 4 → ℕ := ![130, 131, 132, 133]
theorem newLabel31_injective : Function.Injective newLabel31 := by decide
theorem fresh31 : ∀ o : Vertex31, ∀ a : Fin 4, o.val ≠ newLabel31 a := by decide
theorem labels31_mem : ∀ a : ({x : Vertex31 // x ≠ v31}) ⊕ (Fin 4),
    Sum.elim oldLabel31 newLabel31 a ∈ vertices32 := by decide
theorem labels31_cover : ∀ t : Vertex32, ∃ a : ({x : Vertex31 // x ≠ v31}) ⊕ (Fin 4),
    Sum.elim oldLabel31 newLabel31 a = t.val := by decide
def labels31 : (({x : Vertex31 // x ≠ v31}) ⊕ (Fin 4)) ≃ Vertex32 :=
  sumLabels vertices32 oldLabel31 newLabel31 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel31_injective (fun o a => fresh31 o.val a) labels31_mem labels31_cover
theorem adjacency31 : ∀ x y : ({x : Vertex31 // x ≠ v31}) ⊕ (Fin 4),
    graph32.Adj (labels31 x) (labels31 y) ↔ (lozinSuspension graph31 v31 Y31 Z31).Adj x y := by decide
theorem mappedGraph31 : (lozinSuspension graph31 v31 Y31 Z31).map labels31 = graph32 :=
  map_eq_of_forward (lozinSuspension graph31 v31 Y31 Z31) graph32 labels31 adjacency31
def chain32 : MoveChain IndependenceComplexTorsionSeed.G0 graph32 32 := by
  simpa only [mappedGraph31] using (MoveChain.lozin chain31 v31 Y31 Z31 partition31 disjoint31 nonempty31 labels31)

/- Certificate operation 32 (0-based): lozin_suspension. -/
def v32 : Vertex32 := ⟨73, by decide⟩
def Y32 : Finset Vertex32 := {⟨42, by decide⟩, ⟨49, by decide⟩}
def Z32 : Finset Vertex32 := {⟨47, by decide⟩, ⟨72, by decide⟩, ⟨44, by decide⟩}
theorem partition32 : ∀ x : Vertex32, graph32.Adj v32 x ↔ x ∈ Y32 ∨ x ∈ Z32 := by decide
theorem disjoint32 : Disjoint Y32 Z32 := by decide
theorem nonempty32 : Y32.Nonempty := by decide
def oldLabel32 : ({x : Vertex32 // x ≠ v32}) → ℕ := fun x => x.val.val
def newLabel32 : Fin 4 → ℕ := ![134, 135, 136, 137]
theorem newLabel32_injective : Function.Injective newLabel32 := by decide
theorem fresh32 : ∀ o : Vertex32, ∀ a : Fin 4, o.val ≠ newLabel32 a := by decide
theorem labels32_mem : ∀ a : ({x : Vertex32 // x ≠ v32}) ⊕ (Fin 4),
    Sum.elim oldLabel32 newLabel32 a ∈ vertices33 := by decide
theorem labels32_cover : ∀ t : Vertex33, ∃ a : ({x : Vertex32 // x ≠ v32}) ⊕ (Fin 4),
    Sum.elim oldLabel32 newLabel32 a = t.val := by decide
def labels32 : (({x : Vertex32 // x ≠ v32}) ⊕ (Fin 4)) ≃ Vertex33 :=
  sumLabels vertices33 oldLabel32 newLabel32 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel32_injective (fun o a => fresh32 o.val a) labels32_mem labels32_cover
theorem adjacency32 : ∀ x y : ({x : Vertex32 // x ≠ v32}) ⊕ (Fin 4),
    graph33.Adj (labels32 x) (labels32 y) ↔ (lozinSuspension graph32 v32 Y32 Z32).Adj x y := by decide
theorem mappedGraph32 : (lozinSuspension graph32 v32 Y32 Z32).map labels32 = graph33 :=
  map_eq_of_forward (lozinSuspension graph32 v32 Y32 Z32) graph33 labels32 adjacency32
def chain33 : MoveChain IndependenceComplexTorsionSeed.G0 graph33 33 := by
  simpa only [mappedGraph32] using (MoveChain.lozin chain32 v32 Y32 Z32 partition32 disjoint32 nonempty32 labels32)

/- Certificate operation 33 (0-based): lozin_suspension. -/
def v33 : Vertex33 := ⟨81, by decide⟩
def Y33 : Finset Vertex33 := {⟨52, by decide⟩, ⟨74, by decide⟩}
def Z33 : Finset Vertex33 := {⟨80, by decide⟩, ⟨54, by decide⟩}
theorem partition33 : ∀ x : Vertex33, graph33.Adj v33 x ↔ x ∈ Y33 ∨ x ∈ Z33 := by decide
theorem disjoint33 : Disjoint Y33 Z33 := by decide
theorem nonempty33 : Y33.Nonempty := by decide
def oldLabel33 : ({x : Vertex33 // x ≠ v33}) → ℕ := fun x => x.val.val
def newLabel33 : Fin 4 → ℕ := ![138, 139, 140, 141]
theorem newLabel33_injective : Function.Injective newLabel33 := by decide
theorem fresh33 : ∀ o : Vertex33, ∀ a : Fin 4, o.val ≠ newLabel33 a := by decide
theorem labels33_mem : ∀ a : ({x : Vertex33 // x ≠ v33}) ⊕ (Fin 4),
    Sum.elim oldLabel33 newLabel33 a ∈ vertices34 := by decide
theorem labels33_cover : ∀ t : Vertex34, ∃ a : ({x : Vertex33 // x ≠ v33}) ⊕ (Fin 4),
    Sum.elim oldLabel33 newLabel33 a = t.val := by decide
def labels33 : (({x : Vertex33 // x ≠ v33}) ⊕ (Fin 4)) ≃ Vertex34 :=
  sumLabels vertices34 oldLabel33 newLabel33 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel33_injective (fun o a => fresh33 o.val a) labels33_mem labels33_cover
theorem adjacency33 : ∀ x y : ({x : Vertex33 // x ≠ v33}) ⊕ (Fin 4),
    graph34.Adj (labels33 x) (labels33 y) ↔ (lozinSuspension graph33 v33 Y33 Z33).Adj x y := by decide
theorem mappedGraph33 : (lozinSuspension graph33 v33 Y33 Z33).map labels33 = graph34 :=
  map_eq_of_forward (lozinSuspension graph33 v33 Y33 Z33) graph34 labels33 adjacency33
def chain34 : MoveChain IndependenceComplexTorsionSeed.G0 graph34 34 := by
  simpa only [mappedGraph33] using (MoveChain.lozin chain33 v33 Y33 Z33 partition33 disjoint33 nonempty33 labels33)

/- Certificate operation 34 (0-based): lozin_suspension. -/
def v34 : Vertex34 := ⟨85, by decide⟩
def Y34 : Finset Vertex34 := {⟨84, by decide⟩, ⟨58, by decide⟩}
def Z34 : Finset Vertex34 := {⟨97, by decide⟩, ⟨22, by decide⟩, ⟨28, by decide⟩}
theorem partition34 : ∀ x : Vertex34, graph34.Adj v34 x ↔ x ∈ Y34 ∨ x ∈ Z34 := by decide
theorem disjoint34 : Disjoint Y34 Z34 := by decide
theorem nonempty34 : Y34.Nonempty := by decide
def oldLabel34 : ({x : Vertex34 // x ≠ v34}) → ℕ := fun x => x.val.val
def newLabel34 : Fin 4 → ℕ := ![142, 143, 144, 145]
theorem newLabel34_injective : Function.Injective newLabel34 := by decide
theorem fresh34 : ∀ o : Vertex34, ∀ a : Fin 4, o.val ≠ newLabel34 a := by decide
theorem labels34_mem : ∀ a : ({x : Vertex34 // x ≠ v34}) ⊕ (Fin 4),
    Sum.elim oldLabel34 newLabel34 a ∈ vertices35 := by decide
theorem labels34_cover : ∀ t : Vertex35, ∃ a : ({x : Vertex34 // x ≠ v34}) ⊕ (Fin 4),
    Sum.elim oldLabel34 newLabel34 a = t.val := by decide
def labels34 : (({x : Vertex34 // x ≠ v34}) ⊕ (Fin 4)) ≃ Vertex35 :=
  sumLabels vertices35 oldLabel34 newLabel34 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel34_injective (fun o a => fresh34 o.val a) labels34_mem labels34_cover
theorem adjacency34 : ∀ x y : ({x : Vertex34 // x ≠ v34}) ⊕ (Fin 4),
    graph35.Adj (labels34 x) (labels34 y) ↔ (lozinSuspension graph34 v34 Y34 Z34).Adj x y := by decide
theorem mappedGraph34 : (lozinSuspension graph34 v34 Y34 Z34).map labels34 = graph35 :=
  map_eq_of_forward (lozinSuspension graph34 v34 Y34 Z34) graph35 labels34 adjacency34
def chain35 : MoveChain IndependenceComplexTorsionSeed.G0 graph35 35 := by
  simpa only [mappedGraph34] using (MoveChain.lozin chain34 v34 Y34 Z34 partition34 disjoint34 nonempty34 labels34)

/- Certificate operation 35 (0-based): lozin_suspension. -/
def v35 : Vertex35 := ⟨89, by decide⟩
def Y35 : Finset Vertex35 := {⟨19, by decide⟩, ⟨88, by decide⟩}
def Z35 : Finset Vertex35 := {⟨59, by decide⟩, ⟨57, by decide⟩, ⟨82, by decide⟩}
theorem partition35 : ∀ x : Vertex35, graph35.Adj v35 x ↔ x ∈ Y35 ∨ x ∈ Z35 := by decide
theorem disjoint35 : Disjoint Y35 Z35 := by decide
theorem nonempty35 : Y35.Nonempty := by decide
def oldLabel35 : ({x : Vertex35 // x ≠ v35}) → ℕ := fun x => x.val.val
def newLabel35 : Fin 4 → ℕ := ![146, 147, 148, 149]
theorem newLabel35_injective : Function.Injective newLabel35 := by decide
theorem fresh35 : ∀ o : Vertex35, ∀ a : Fin 4, o.val ≠ newLabel35 a := by decide
theorem labels35_mem : ∀ a : ({x : Vertex35 // x ≠ v35}) ⊕ (Fin 4),
    Sum.elim oldLabel35 newLabel35 a ∈ vertices36 := by decide
theorem labels35_cover : ∀ t : Vertex36, ∃ a : ({x : Vertex35 // x ≠ v35}) ⊕ (Fin 4),
    Sum.elim oldLabel35 newLabel35 a = t.val := by decide
def labels35 : (({x : Vertex35 // x ≠ v35}) ⊕ (Fin 4)) ≃ Vertex36 :=
  sumLabels vertices36 oldLabel35 newLabel35 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel35_injective (fun o a => fresh35 o.val a) labels35_mem labels35_cover
theorem adjacency35 : ∀ x y : ({x : Vertex35 // x ≠ v35}) ⊕ (Fin 4),
    graph36.Adj (labels35 x) (labels35 y) ↔ (lozinSuspension graph35 v35 Y35 Z35).Adj x y := by decide
theorem mappedGraph35 : (lozinSuspension graph35 v35 Y35 Z35).map labels35 = graph36 :=
  map_eq_of_forward (lozinSuspension graph35 v35 Y35 Z35) graph36 labels35 adjacency35
def chain36 : MoveChain IndependenceComplexTorsionSeed.G0 graph36 36 := by
  simpa only [mappedGraph35] using (MoveChain.lozin chain35 v35 Y35 Z35 partition35 disjoint35 nonempty35 labels35)

/- Certificate operation 36 (0-based): lozin_suspension. -/
def v36 : Vertex36 := ⟨97, by decide⟩
def Y36 : Finset Vertex36 := {⟨64, by decide⟩, ⟨62, by decide⟩}
def Z36 : Finset Vertex36 := {⟨145, by decide⟩, ⟨96, by decide⟩}
theorem partition36 : ∀ x : Vertex36, graph36.Adj v36 x ↔ x ∈ Y36 ∨ x ∈ Z36 := by decide
theorem disjoint36 : Disjoint Y36 Z36 := by decide
theorem nonempty36 : Y36.Nonempty := by decide
def oldLabel36 : ({x : Vertex36 // x ≠ v36}) → ℕ := fun x => x.val.val
def newLabel36 : Fin 4 → ℕ := ![150, 151, 152, 153]
theorem newLabel36_injective : Function.Injective newLabel36 := by decide
theorem fresh36 : ∀ o : Vertex36, ∀ a : Fin 4, o.val ≠ newLabel36 a := by decide
theorem labels36_mem : ∀ a : ({x : Vertex36 // x ≠ v36}) ⊕ (Fin 4),
    Sum.elim oldLabel36 newLabel36 a ∈ vertices37 := by decide
theorem labels36_cover : ∀ t : Vertex37, ∃ a : ({x : Vertex36 // x ≠ v36}) ⊕ (Fin 4),
    Sum.elim oldLabel36 newLabel36 a = t.val := by decide
def labels36 : (({x : Vertex36 // x ≠ v36}) ⊕ (Fin 4)) ≃ Vertex37 :=
  sumLabels vertices37 oldLabel36 newLabel36 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel36_injective (fun o a => fresh36 o.val a) labels36_mem labels36_cover
theorem adjacency36 : ∀ x y : ({x : Vertex36 // x ≠ v36}) ⊕ (Fin 4),
    graph37.Adj (labels36 x) (labels36 y) ↔ (lozinSuspension graph36 v36 Y36 Z36).Adj x y := by decide
theorem mappedGraph36 : (lozinSuspension graph36 v36 Y36 Z36).map labels36 = graph37 :=
  map_eq_of_forward (lozinSuspension graph36 v36 Y36 Z36) graph37 labels36 adjacency36
def chain37 : MoveChain IndependenceComplexTorsionSeed.G0 graph37 37 := by
  simpa only [mappedGraph36] using (MoveChain.lozin chain36 v36 Y36 Z36 partition36 disjoint36 nonempty36 labels36)

/- Certificate operation 37 (0-based): lozin_suspension. -/
def v37 : Vertex37 := ⟨137, by decide⟩
def Y37 : Finset Vertex37 := {⟨136, by decide⟩, ⟨44, by decide⟩}
def Z37 : Finset Vertex37 := {⟨72, by decide⟩, ⟨47, by decide⟩}
theorem partition37 : ∀ x : Vertex37, graph37.Adj v37 x ↔ x ∈ Y37 ∨ x ∈ Z37 := by decide
theorem disjoint37 : Disjoint Y37 Z37 := by decide
theorem nonempty37 : Y37.Nonempty := by decide
def oldLabel37 : ({x : Vertex37 // x ≠ v37}) → ℕ := fun x => x.val.val
def newLabel37 : Fin 4 → ℕ := ![154, 155, 156, 157]
theorem newLabel37_injective : Function.Injective newLabel37 := by decide
theorem fresh37 : ∀ o : Vertex37, ∀ a : Fin 4, o.val ≠ newLabel37 a := by decide
theorem labels37_mem : ∀ a : ({x : Vertex37 // x ≠ v37}) ⊕ (Fin 4),
    Sum.elim oldLabel37 newLabel37 a ∈ vertices38 := by decide
theorem labels37_cover : ∀ t : Vertex38, ∃ a : ({x : Vertex37 // x ≠ v37}) ⊕ (Fin 4),
    Sum.elim oldLabel37 newLabel37 a = t.val := by decide
def labels37 : (({x : Vertex37 // x ≠ v37}) ⊕ (Fin 4)) ≃ Vertex38 :=
  sumLabels vertices38 oldLabel37 newLabel37 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel37_injective (fun o a => fresh37 o.val a) labels37_mem labels37_cover
theorem adjacency37 : ∀ x y : ({x : Vertex37 // x ≠ v37}) ⊕ (Fin 4),
    graph38.Adj (labels37 x) (labels37 y) ↔ (lozinSuspension graph37 v37 Y37 Z37).Adj x y := by decide
theorem mappedGraph37 : (lozinSuspension graph37 v37 Y37 Z37).map labels37 = graph38 :=
  map_eq_of_forward (lozinSuspension graph37 v37 Y37 Z37) graph38 labels37 adjacency37
def chain38 : MoveChain IndependenceComplexTorsionSeed.G0 graph38 38 := by
  simpa only [mappedGraph37] using (MoveChain.lozin chain37 v37 Y37 Z37 partition37 disjoint37 nonempty37 labels37)

/- Certificate operation 38 (0-based): lozin_suspension. -/
def v38 : Vertex38 := ⟨145, by decide⟩
def Y38 : Finset Vertex38 := {⟨153, by decide⟩, ⟨144, by decide⟩}
def Z38 : Finset Vertex38 := {⟨28, by decide⟩, ⟨22, by decide⟩}
theorem partition38 : ∀ x : Vertex38, graph38.Adj v38 x ↔ x ∈ Y38 ∨ x ∈ Z38 := by decide
theorem disjoint38 : Disjoint Y38 Z38 := by decide
theorem nonempty38 : Y38.Nonempty := by decide
def oldLabel38 : ({x : Vertex38 // x ≠ v38}) → ℕ := fun x => x.val.val
def newLabel38 : Fin 4 → ℕ := ![158, 159, 160, 161]
theorem newLabel38_injective : Function.Injective newLabel38 := by decide
theorem fresh38 : ∀ o : Vertex38, ∀ a : Fin 4, o.val ≠ newLabel38 a := by decide
theorem labels38_mem : ∀ a : ({x : Vertex38 // x ≠ v38}) ⊕ (Fin 4),
    Sum.elim oldLabel38 newLabel38 a ∈ vertices39 := by decide
theorem labels38_cover : ∀ t : Vertex39, ∃ a : ({x : Vertex38 // x ≠ v38}) ⊕ (Fin 4),
    Sum.elim oldLabel38 newLabel38 a = t.val := by decide
def labels38 : (({x : Vertex38 // x ≠ v38}) ⊕ (Fin 4)) ≃ Vertex39 :=
  sumLabels vertices39 oldLabel38 newLabel38 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel38_injective (fun o a => fresh38 o.val a) labels38_mem labels38_cover
theorem adjacency38 : ∀ x y : ({x : Vertex38 // x ≠ v38}) ⊕ (Fin 4),
    graph39.Adj (labels38 x) (labels38 y) ↔ (lozinSuspension graph38 v38 Y38 Z38).Adj x y := by decide
theorem mappedGraph38 : (lozinSuspension graph38 v38 Y38 Z38).map labels38 = graph39 :=
  map_eq_of_forward (lozinSuspension graph38 v38 Y38 Z38) graph39 labels38 adjacency38
def chain39 : MoveChain IndependenceComplexTorsionSeed.G0 graph39 39 := by
  simpa only [mappedGraph38] using (MoveChain.lozin chain38 v38 Y38 Z38 partition38 disjoint38 nonempty38 labels38)

/- Certificate operation 39 (0-based): lozin_suspension. -/
def v39 : Vertex39 := ⟨149, by decide⟩
def Y39 : Finset Vertex39 := {⟨82, by decide⟩, ⟨57, by decide⟩}
def Z39 : Finset Vertex39 := {⟨59, by decide⟩, ⟨148, by decide⟩}
theorem partition39 : ∀ x : Vertex39, graph39.Adj v39 x ↔ x ∈ Y39 ∨ x ∈ Z39 := by decide
theorem disjoint39 : Disjoint Y39 Z39 := by decide
theorem nonempty39 : Y39.Nonempty := by decide
def oldLabel39 : ({x : Vertex39 // x ≠ v39}) → ℕ := fun x => x.val.val
def newLabel39 : Fin 4 → ℕ := ![162, 163, 164, 165]
theorem newLabel39_injective : Function.Injective newLabel39 := by decide
theorem fresh39 : ∀ o : Vertex39, ∀ a : Fin 4, o.val ≠ newLabel39 a := by decide
theorem labels39_mem : ∀ a : ({x : Vertex39 // x ≠ v39}) ⊕ (Fin 4),
    Sum.elim oldLabel39 newLabel39 a ∈ vertices40 := by decide
theorem labels39_cover : ∀ t : Vertex40, ∃ a : ({x : Vertex39 // x ≠ v39}) ⊕ (Fin 4),
    Sum.elim oldLabel39 newLabel39 a = t.val := by decide
def labels39 : (({x : Vertex39 // x ≠ v39}) ⊕ (Fin 4)) ≃ Vertex40 :=
  sumLabels vertices40 oldLabel39 newLabel39 (Subtype.val_injective.comp Subtype.val_injective)
    newLabel39_injective (fun o a => fresh39 o.val a) labels39_mem labels39_cover
theorem adjacency39 : ∀ x y : ({x : Vertex39 // x ≠ v39}) ⊕ (Fin 4),
    graph40.Adj (labels39 x) (labels39 y) ↔ (lozinSuspension graph39 v39 Y39 Z39).Adj x y := by decide
theorem mappedGraph39 : (lozinSuspension graph39 v39 Y39 Z39).map labels39 = graph40 :=
  map_eq_of_forward (lozinSuspension graph39 v39 Y39 Z39) graph40 labels39 adjacency39
def chain40 : MoveChain IndependenceComplexTorsionSeed.G0 graph40 40 := by
  simpa only [mappedGraph39] using (MoveChain.lozin chain39 v39 Y39 Z39 partition39 disjoint39 nonempty39 labels39)

/-- Exactly the preserved JSON Nat vertex list; no new coordinate numbering. -/
abbrev concreteSubcubicVertexList := vertexList40
abbrev concreteSubcubicVertices := vertices40
abbrev ConcreteSubcubicVertex := Vertex40
/-- Exactly the preserved JSON list of 178 unordered Nat edge pairs. -/
abbrev concreteSubcubicEdges := edges40
def concreteSubcubicGraph : SimpleGraph ConcreteSubcubicVertex :=
  listGraph concreteSubcubicVertices concreteSubcubicEdges

theorem finalGraphIdentity : concreteSubcubicGraph = graph40 := rfl

/-- The chain begins at the actual seed supplier's H.compl. Every constructor
consumes its exact finite hypotheses and its actual label equivalence. -/
def fortyMoves : MoveChain IndependenceComplexTorsionSeed.G0 concreteSubcubicGraph 40 := by
  rw [finalGraphIdentity]
  exact chain40

/-- Consumes the literal forty-constructor chain and the supplier's genuine
reduced integral singular homology shift. No homology transport is assumed. -/
def reducedHomologyIso (q : ℕ) (hq : 1 ≤ q) :
    Reduced concreteSubcubicGraph (q + 40) ≅ Reduced IndependenceComplexTorsionSeed.G0 q :=
  fortyMoves.reducedHomologyIso q hq

end D5.S3.Geometry.KingFiniteReplay
