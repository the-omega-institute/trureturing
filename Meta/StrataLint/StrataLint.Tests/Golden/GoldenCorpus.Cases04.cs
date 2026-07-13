using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class GoldenCorpus
{
    private static GoldenCase[] Corpus4 { get; } =
    [
        C(
            "missing-exact-evidence-mirror",
            [],
            [Mirror(false, false)],
            [D(4, RingPath, "missing evidence mirror Evidence/D5/S0/Carrier/Ring.result.json")]),
        C(
            "duplicate-task-code",
            [],
            [T("D5/X_Frontier/TaskOne.lean", "D5/X_Frontier/TaskOne", "D5-T0095"), T("D5/X_Frontier/TaskTwo.lean", "D5/X_Frontier/TaskTwo", "D5-T0095")],
            [D(13, "D5/X_Frontier/TaskOne.lean", "task code D5-T0095 is duplicated")]),
        C(
            "format-only-fabricated-doi-under-D5-T0012",
            [],
            [W("Library/queries.yaml", "schema_version: 1\nqueries:\n  - id: D5-Q0094\n    query: format-only fixture under explicit existence deferral\n    target_gid: D5/S0/Carrier/Ring\n    bibkey: fixture2026paper\n    doi: 10.9999/definitely-fabricated-r2\n")],
            []),
        C(
            "malformed-doi-format",
            [],
            [W("Library/queries.yaml", "schema_version: 1\nqueries:\n  - id: D5-Q0089\n    query: malformed identifier fixture\n    target_gid: D5/S0/Carrier/Ring\n    bibkey: malformed2026paper\n    doi: definitely-not-a-doi\n")],
            [D(17, "Library/queries.yaml", "query D5-Q0089 needs DOI/arXiv or a pending case")]),
        C(
            "unattested-values-are-rejected",
            [],
            [W("Evidence/D5/values.result.json", "{\"D5/sample\": {\"value\": 123}}\n")],
            [D(18, "Evidence/D5/values.result.json", "canonical values projection must be Evidence/D5/values.json")]),
        C(
            "handwritten-verified-values-are-rejected",
            [],
            [W("Evidence/D5/values.result.json", "{\"D5/sample\": {\"status\": \"verified\", \"value\": 123}}\n")],
            [D(18, "Evidence/D5/values.result.json", "canonical values projection must be Evidence/D5/values.json")]),
        C(
            "root-protected-axiom",
            [],
            [W("Trureturing.lean", "namespace RootProbe\nprotected axiom rootProtectedBypass : False\nend RootProbe\n")],
            [D(20, "Trureturing.lean", "axiom declarations are confined to AxiomDebt.lean: RootProbe.rootProtectedBypass")]),
        C(
            "hearts-file-deletion",
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by sorry\n")],
            [X(HeartsPath)],
            [D(8, HeartsPath, "frozen Hearts.lean was deleted")]),
        C(
            "hearts-baseline-inspection-fails",
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : := broken\n")],
            [L(HeartsPath, "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by sorry\n")],
            [D(8, HeartsPath, "protected Hearts baseline has no semantic report")]),
        C(
            "noncanonical-e-directory-double-artifact",
            [],
            [W("Evidence/D5/S0/Carrier/Ring/result.json", "{}\n"), W("Evidence/D5/S0/Carrier/Ring/alternate.json", "{}\n")],
            [D(0, "Evidence/D5/S0/Carrier/Ring/alternate.json", "noncanonical Evidence artifact: Evidence filename needs module.selector.kind"), D(0, "Evidence/D5/S0/Carrier/Ring/result.json", "noncanonical Evidence artifact: Evidence filename needs module.selector.kind")]),
        C(
            "noncanonical-query-target",
            [],
            [T("D5/X_Frontier/QueryTargetTask.lean", "D5/X_Frontier/QueryTargetTask", "D5-T0093"), W("Library/queries.yaml", "schema_version: 1\nqueries:\n  - id: D5-Q0093\n    query: old evidence address\n    target_gid: D5/E/S3/Analytic/Cphi\n    pending_case: D5-T0093\n")],
            [D(17, "Library/queries.yaml", "query D5-Q0093 has noncanonical target: Evidence GID needs an explicit supported artifact kind tag")]),
        C(
            "managed-early-exit-hides-axiom",
            [],
            [L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import Lean.Elab.Command\n\nnamespace ExitProbe\nprotected axiom earlyExitBypass : False\nend ExitProbe\n\nrun_cmd do (IO.Process.exit 0 : IO Unit)\n")],
            [D(20, RingPath, "Lean environment inspection failed: compiler exited successfully without complete module artifacts")]),
        C(
            "candidate-marker-forgery-cannot-register-debt",
            [],
            [L(AssumptionDebtPath, "D5/X_Assumptions/AxiomDebt", Generality.Instance, "import Lean.Elab.Command\n\nrun_cmd IO.println \"STRATALINT_TRUSTED_LEAN_JSON\\t{\\\"name\\\":\\\"sharedForgedDebt\\\",\\\"kind\\\":\\\"axiom\\\",\\\"type\\\":\\\"False\\\",\\\"axioms\\\":[\\\"sharedForgedDebt\\\"]}\"\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "axiom sharedForgedDebt : False\n")],
            [D(20, RingPath, "axiom declarations are confined to AxiomDebt.lean: sharedForgedDebt")]),
        C(
            "candidate-stdout-decoy-is-isolated",
            [],
            [L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import Lean.Elab.Command\n\nrun_cmd IO.println \"STRATALINT_LEAN_JSON\\tnot-json\"\ndef stdoutSafe : Nat := 0\n")],
            []),
        C(
            "quoted-import-generality",
            [],
            [L(NotationPath, "D5/S0/Conventions/Notation", Generality.Instance, "def quotedInstanceFact : Nat := 1\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import «D5».S0.Conventions.Notation\n\ndef quotedGeneral : Nat := 0\n")],
            [D(10, RingPath, "G artifact imports I fact D5/S0/Conventions/Notation.lean")]),
        C(
            "quoted-import-same-layer",
            [],
            [L(NotationPath, "D5/S0/Conventions/Notation", Generality.General, "def quotedGeneralFact : Nat := 1\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import «D5».S0.Conventions.Notation\n\ndef quotedConsumer : Nat := quotedGeneralFact\n")],
            []),
        C(
            "duplicate-debt-axiom-name",
            [],
            [L(AssumptionDebtPath, "D5/X_Assumptions/AxiomDebt", Generality.Instance, "axiom sharedDebtName : False\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "axiom sharedDebtName : False\n")],
            [D(20, RingPath, "axiom declarations are confined to AxiomDebt.lean: sharedDebtName")]),
        C(
            "registered-debt-through-import",
            [],
            [L(AssumptionDebtPath, "D5/X_Assumptions/AxiomDebt", Generality.Instance, "axiom registeredDebt : False\n"), L("D5/X_Certificates/ConditionalResult.lean", "D5/X_Certificates/ConditionalResult", Generality.Instance, "import D5.X_Assumptions.AxiomDebt\n\ntheorem conditionalResult : False := registeredDebt\n")],
            []),
        C(
            "private-axiom-is-inspected",
            [],
            [L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "private axiom hiddenAxiom : False\n")],
            [D(20, RingPath, "axiom declarations are confined to AxiomDebt.lean: _private.D5.S0.Carrier.Ring.0.hiddenAxiom")]),
        C(
            "root-imports-frontier",
            [],
            [L("D5/X_Frontier/OpenProbe.lean", "D5/X_Frontier/OpenProbe", Generality.Extremal, "theorem openProbe : True := by sorry\n"), W("Trureturing.lean", "import D5.X_Frontier.OpenProbe\n")],
            [D(1, "Trureturing.lean", "stratum closure may not import D5/X_Frontier/OpenProbe.lean")]),
        C(
            "in-memory-import-uses-current-graph",
            [],
            [L("D5/S0/Carrier/FixtureDependency.lean", "D5/S0/Carrier/FixtureDependency", Generality.General, "def fixtureDependency : Nat := 7\n"), L(RingPath, "D5/S0/Carrier/Ring", Generality.General, "import D5.S0.Carrier.FixtureDependency\n\ndef currentGraphConsumer : Nat := fixtureDependency\n")],
            []),
        C(
            "future-blueprint-is-uninstantiated",
            [],
            [W("Blueprint/D8/S0/Carrier/Ring.md", "future blueprint\n")],
            [D(21, "Blueprint/D8/S0/Carrier/Ring.md", "D8 未实例化(压力未至,D5-T0009)")]),
        C(
            "future-evidence-is-uninstantiated",
            [],
            [W("Evidence/D8/S0/Carrier/Ring.result.json", "{}\n")],
            [D(21, "Evidence/D8/S0/Carrier/Ring.result.json", "D8 未实例化(压力未至,D5-T0009)")]),
        C(
            "foreign-theory-task-code",
            [],
            [T("D5/X_Frontier/ForeignTask.lean", "D5/X_Frontier/ForeignTask", "D8-T0092")],
            [D(13, "D5/X_Frontier/ForeignTask.lean", "task block does not match the A7 grammar")]),
        C(
            "valid-query-source-fragment",
            [],
            [W("Library/notes/provenance.md", "heading\nanchor line\n"), W("Library/queries.yaml", "schema_version: 1\nhash_contract: sha256-of-exact-utf8-source-line-including-lf\nqueries:\n  - id: D5-Q0091\n    query: exact source anchor\n    target_gid: D5/S0/Carrier/Ring\n    bibkey: fixture2026source\n    doi: 10.1000/source\n    source_path: Library/notes/provenance.md\n    source_line: 2\n    fragment_sha256: b5c686f3f769df23314c0caa3daa49bb9512452f3094e1799c0b7f2ae83c6500\n")],
            []),
        C(
            "query-source-fragment-hash-mismatch",
            [],
            [W("Library/notes/provenance.md", "heading\nanchor line\n"), W("Library/queries.yaml", "schema_version: 1\nhash_contract: sha256-of-exact-utf8-source-line-including-lf\nqueries:\n  - id: D5-Q0090\n    query: stale source anchor\n    target_gid: D5/S0/Carrier/Ring\n    bibkey: fixture2026stale\n    doi: 10.1000/stale\n    source_path: Library/notes/provenance.md\n    source_line: 2\n    fragment_sha256: b5c686f3f769df23314c0caa3daa49bb9512452f3094e1799c0b7f2ae83c6501\n")],
            []),
        C(
            "values-without-producer-attestation-are-rejected",
            [],
            [W("Evidence/D5/values.result.json", "{\"D5/sample\": {\"status\": \"verified\", \"value\": 123}}\n")],
            [D(18, "Evidence/D5/values.result.json", "canonical values projection must be Evidence/D5/values.json")]),
    ];
}
