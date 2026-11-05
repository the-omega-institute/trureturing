import LeanInformationAudit.CompiledSourceScope
import LeanInformationAudit.CompiledSourceContract
import LeanInformationAudit.ArtifactRegistration
import LeanInformationAudit.CompiledAxioms

open Lean LeanInformationAudit

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let scratch : System.FilePath := args.head!
  searchPathRef.modify (scratch :: ·)
  let owner := `Reg.D5.S3.Topology.Measures.RegularSignedLift
  let target := `D5.S3.Topology.Measures.RegularSignedLift.regular_add
  let ns := owner ++ `TopologyOccurrenceCandidate
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  RawArtifacts.loadModule owner reader
  RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
  let store ← reader.get
  let some info := store.constants.find? target | throw <| IO.userError "target_missing"
  let some arenaInfo := store.constants.find? (ns ++ `arena) | throw <| IO.userError "candidate_arena_missing"
  let levels := info.levelParams.map Level.param
  unless arenaInfo.levelParams.length == info.levelParams.length do
    throw <| IO.userError "rigid_universe_mismatch"
  let ctx ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store owner {} (({} : NameSet).insert target)
  let action : CompiledSourceScope.M Unit := do
    let selected : SourceSelection := { owner := `D5.S3.Topology.Measures.RegularSignedLift,
      coordinates := #[0], readouts := #[{path := Array.replicate 10 "body" ++ #["fn", "arg"], stateBinder := 1}] }
    let scope ← CompiledSourceScope.resolve info selected
    let arena := mkConst (ns ++ `arena) levels
    let actual := mkConst (ns ++ `actual) levels
    let signature ← CompiledSourceScope.projectField `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.signature arena
    let law ← CompiledSourceScope.projectField `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law arena #[actual]
    CompiledSourceScope.reconstruct scope.expanded law
    CompiledSourceScope.validateFields scope signature actual
    IO.println (Json.compress <| Json.mkObj [("scope", toJson "accepted"),
      ("target", toJson target.toString), ("levels", toJson scope.levels.length),
      ("telescope", toJson scope.telescope.size), ("coordinates", toJson selected.coordinates),
      ("readouts", toJson scope.readouts.size), ("raw_observation", toJson (reprStr scope.readouts[0]!.rawObservation)),
      ("state", toJson (reprStr scope.readouts[0]!.state)),
      ("output", toJson (reprStr scope.readouts[0]!.output)),
      ("projected", toJson (reprStr scope.readouts[0]!.projected))])
  discard <| (action.run 524288).run ctx
  let closures ← IO.mkRef ({} : CompiledAxioms.AxiomClosureState)
  for name in #[target, ns ++ `source_bridge, ns ++ `actual_positive, ns ++ `rejected_law,
      ns ++ `actual_dependence, ns ++ `familyRegistration, ns ++ `registration] do
    let axioms ← CompiledAxioms.collectAxiomsShared store.constants.find? closures name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throw <| IO.userError s!"nonstandard_axioms:{name}:{axioms}"
    IO.println (Json.compress <| Json.mkObj [("declaration",toJson name.toString),("axioms",toJson (axioms.map Name.toString))])
  let reachable := reachableModules (ArtifactRegistration.importsOf store) owner
  let owners := store.moduleOrder.filter (fun m => reachable.contains m && (`Reg).isPrefixOf m)
  let context := CompiledRegistration.expressionContext store.constants.find? (← IO.getNumHeartbeats) {}
  let snapshot ← Contract.Discovery.discoverCompiled #[] owners context
    (fun m => return (← store.getModule m).constants)
    (CompiledAxioms.collectAxiomsShared store.constants.find? closures)
  let assess : ArtifactRegistration.M Unit := do
    ArtifactRegistration.prepareSnapshot snapshot
    let records ← ArtifactRegistration.assessJoined owner
    modify fun state => {state with records}
  let (_, assessed) ← assess.run {store}
  let result ← ArtifactRegistration.targetJson owner assessed
  IO.FS.writeFile (scratch / "private-binding.json") (result.pretty ++ "\n")
  IO.println result.compress
