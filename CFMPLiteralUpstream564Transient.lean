import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Injective
import Lean.Util.CollectAxioms

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in #[``AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_injective,
      ``AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_surjective,
      ``AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_bijective] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP564 missing checked upstream declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP564 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP564 CHECKED {name} axioms={axioms}"
