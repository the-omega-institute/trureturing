/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourModelDistances
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-four-half-embedding-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Walk.Basic]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourHalfEmbedding.no_twenty_four_half; instance=D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourHalfEmbedding.no_twenty_four_half
   digest: Certify the distance rows and parent edges of the expanded catalog models. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-! Match the compressed parity graphs to the packed models used by the
coordinate search and certify the graph walks behind its distance bounds. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances

open SimpleGraph
open private adjacent decode from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private graphEdges crosses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
open private Model from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck

open private models from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourEmbeddingCheck in
private def modelAt (index : Fin 53) : Model := models[index.val]!

open private models from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors in
private def colorAt (index : Fin 53) : Nat × Nat := models[index.val]!

private def subdivisionPairs (code color : Nat) : List (Nat × Nat) :=
  (graphEdges (decode code)).filter fun p => !(crosses color p.1 p.2)

private def expandedAdjacent (code color : Nat) (i j : Nat) : Bool :=
  if i < 12 then
    if j < 12 then adjacent (decode code) i j && crosses color i j
    else let p := (subdivisionPairs code color)[j - 12]!
         i == p.1 || i == p.2
  else if j < 12 then
    let p := (subdivisionPairs code color)[i - 12]!
    j == p.1 || j == p.2
  else false

private def distance (model : Model) (i j : Nat) : Nat :=
  if i = j then 0
  else let (lo, hi) := if i < j then (i, j) else (j, i)
       (model[hi - 1]!.2 >>> (4 * lo)) &&& 15

private def reorderings : Array Nat := #[
  0xaaee4a5a4a88e6f4b4c27060c41ca0, 0x9c124a4ae38beaa408cbb04ee69580,
  0x8dd331ca073068bb3aaa795ac20900, 0x9de291c14e119a1a1175b3e47620a0,
  0xadd32252cf340510b97350ce56b100, 0xab9a1592898987280957b4de7620a0,
  0xbcd3179a84142437056ab55076b0a0, 0xbbcd14cea3a04ed909c8242cb51580,
  0xa5493ba646839eb88aca184e56b100, 0x9d095ba576305ee88e42829056b0e0,
  0xa493033aa488a637856abd9076b0a0, 0xa5d311c95678a06992a172ce56b100,
  0x8c87055d22335c1a1175b3e67620a0, 0x9b6833bee909ab08c84e4117651580,
  0xb497414226bba6a38ea9795ac20500, 0x85155145e394ee60b936591056b0e0,
  0x9d14fa920bb8e487592168a2661ca0, 0xbd89594c4b8a9c678603a24e56b100,
  0xa597024de2544754bae60c9a7620a0, 0x95d751461451263b25ee305076b0a0,
  0xad09382a227dcc80ba433b589b2ca0, 0x959751461454c77399e92b58171100,
  0x94450aacb66508d439e14cd46b8ce0, 0xbc602339749a8921bc29b55076b0a0,
  0x9445055663a1ccf0bac44358bba4a0, 0x9d517259c3a49717860231dac524a0,
  0xb5095449d180826bbd5348ce56b160, 0x9b93668648a10aa855e28b166b8ce0,
  0xa4c72435c1399e4ac0568b16aba4a0, 0xa4c6973516256eb8c1427864661ca0,
  0xabd77252703c8764b4c27062c520a0, 0xb54945c602334e3938337a18aba4a0,
  0x750b50be0ab5cc8146433b5899ac80, 0xbd8d1a2aa50c1e79b5c81486b49180,
  0x98eb4bd8d0144ee7a1ac5864552480, 0x8cc723b977096afb1a0243589a2880,
  0xbcd7634943140ee7a1aca8625a2480, 0xaaef1b41533168e48a48791ac184e0,
  0xbbcd65cea28c2850b91250ce46b120, 0x8d9541cae6589f343aa50c1a961c80,
  0xadd72b4546a0e029a1ee285276b080, 0xac9771c5c76d94c24de1440c5a0920,
  0xbcd75b1851824af0ba433b58aa2080, 0x826d31c6ab35e85609c8905ed51c80,
  0xbd14e35a25abe4b48da78083341180, 0x758d71412b1c6afa15a144e4762880,
  0x7dcd6145759c2850b91248ce46b140, 0xac97088ec979af42b4ec505c29a080,
  0x6d4b492de2b9ad11a6680c1c4628e0, 0x8c850b2ee648eb3a21ee285476b080,
  0x9553733c50a22635bac50c5aa61c80, 0xad0af0b9109ae42b9ad148ce46b140,
  0x8445343dc1a968bb9ac3924e46b140]

private def reorder (index : Fin 53) (i : Fin 24) : Nat :=
  (reorderings[index.val]! >>> (5 * i.val)) &&& 31

private def valid (index : Fin 53) : Prop :=
  let model := modelAt index
  let (code, color) := colorAt index
  model.length = 23 ∧
    (subdivisionPairs code color).length = 12 ∧
    (∀ i : Fin 24, reorder index i < 24) ∧
    (∀ i j : Fin 24, reorder index i = reorder index j → i = j) ∧
    (∀ i j : Fin 24,
      distance model i.val j.val = 1 ↔
        expandedAdjacent code color (reorder index i) (reorder index j) = true) ∧
    (∀ i : Fin 23, let parent := model[i.val]!.1
      parent < i.val + 1 ∧ distance model (i.val + 1) parent = 1) ∧
    (∀ i j : Fin 24, i ≠ j → 0 < distance model i.val j.val ∧
      ∃ k : Fin 24, distance model i.val k.val = 1 ∧
        distance model k.val j.val + 1 = distance model i.val j.val)

private instance (index : Fin 53) : Decidable (valid index) := by
  unfold valid
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 120000000 in
private theorem valid_model (index : Fin 53) : valid index := by
  fin_cases index <;> decide +kernel

private theorem walk_of_distance {V : Type*} {G : SimpleGraph V} (model : Model)
    (point : Fin 24 → V)
    (hEdge : ∀ i j : Fin 24, distance model i.val j.val = 1 → G.Adj (point i) (point j))
    (hStep : ∀ i j : Fin 24, i ≠ j → 0 < distance model i.val j.val ∧
      ∃ k : Fin 24, distance model i.val k.val = 1 ∧
        distance model k.val j.val + 1 = distance model i.val j.val)
    (i j : Fin 24) : ∃ w : G.Walk (point i) (point j), w.length = distance model i.val j.val := by
  generalize he : distance model i.val j.val = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
    by_cases eq : i = j
    · subst j
      exact ⟨.nil, by simpa [distance] using he⟩
    · obtain ⟨_, k, hk, hkd⟩ := hStep i j eq
      obtain ⟨w, hw⟩ := ih (distance model k.val j.val) (by omega) k j rfl
      exact ⟨.cons (hEdge i k hk) w, by rw [Walk.length_cons, hw, hkd, he]⟩

#print axioms valid_model
#print axioms walk_of_distance

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourModelDistances
