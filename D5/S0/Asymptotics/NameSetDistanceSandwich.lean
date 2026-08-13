/- GID: D5/S0/Asymptotics/NameSetDistanceSandwich
   generality: G
   mirror-B: D5/B/S0/Asymptotics/NameSetDistanceSandwich
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nested nonempty name sets give the reversed infimum-distance sandwich; this closes only the metric consequence in clause (a), while the coding embeddings and clause (b) remain unresolved. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace D5.S0.Asymptotics.NameSetDistanceSandwich

variable {α : Type*} [PseudoMetricSpace α]

/-- Once the budget shifts have been absorbed into three nested name sets, distance to those
sets decreases along the inclusions. Nonemptiness of the smallest set is necessary for real-valued
`Metric.infDist`, whose value on the empty set is zero. -/
theorem nested_name_set_infDist_sandwich
    (x : α) {prefixNames testNames programNames : Set α}
    (hPrefixTest : prefixNames ⊆ testNames)
    (hTestProgram : testNames ⊆ programNames)
    (hPrefix : prefixNames.Nonempty) :
    Metric.infDist x prefixNames ≥ Metric.infDist x testNames ∧
      Metric.infDist x testNames ≥ Metric.infDist x programNames := by
  constructor
  · exact Metric.infDist_le_infDist_of_subset hPrefixTest hPrefix
  · exact Metric.infDist_le_infDist_of_subset hTestProgram (hPrefix.mono hPrefixTest)

end D5.S0.Asymptotics.NameSetDistanceSandwich
