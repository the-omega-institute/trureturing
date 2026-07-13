using StrataLint.Engine;

namespace StrataLint.Tests;

internal static partial class GoldenCorpus
{
    private static GoldenCase[] Corpus2 { get; } =
    [
        C(
            "illegal-formula-character",
            [],
            [W("Evidence/D5/S0/Carrier/Formula.check.json", "{\"formula\": \"sqrt@5\", \"refs\": {}}\n")],
            [D(15, "Evidence/D5/S0/Carrier/Formula.check.json", "illegal formula character '@'")]),
        C(
            "unbound-formula-reference",
            [],
            [W("Evidence/D5/S0/Carrier/Formula.check.json", "{\"formula\": \"2*T0\", \"refs\": {}}\n")],
            [D(15, "Evidence/D5/S0/Carrier/Formula.check.json", "unbound formula ref T0")]),
        C(
            "unregistered-axiom",
            [],
            [L("D5/S0/Carrier/Ring.lean", "D5/S0/Carrier/Ring", Generality.General, "axiom invented : False\n")],
            [D(20, "D5/S0/Carrier/Ring.lean", "axiom declarations are confined to AxiomDebt.lean: invented")]),
        C(
            "unknown-top-level-file",
            [],
            [W("rogue.txt", "closed world\n")],
            [D(0, "rogue.txt", "unknown top-level artifact")]),
        C(
            "unknown-artifact-extension",
            [],
            [W("Evidence/D5/blob.exe", "closed world\n")],
            [D(0, "Evidence/D5/blob.exe", "noncanonical Evidence artifact: Evidence filename needs module.selector.kind")]),
        C(
            "unknown-frozen-paper-extension",
            [],
            [W("Papers/frozen/D5-P001/blob.exe", "closed world\n")],
            [D(0, "Papers/frozen/D5-P001/blob.exe", "noncanonical Papers artifact: path is not a canonical semantic artifact")]),
        C(
            "lowercase-formal-module",
            [],
            [L("D5/S0/Carrier/lowercase.lean", "D5/S0/Carrier/lowercase", Generality.General, "def lowercase : Nat := 0\n")],
            [D(0, "D5/S0/Carrier/lowercase.lean", "noncanonical formal artifact: formal module must be CamelCase")]),
        C(
            "lowercase-evidence-module",
            [],
            [W("Evidence/D5/S0/Carrier/lowercase.result.json", "{}\n")],
            [D(0, "Evidence/D5/S0/Carrier/lowercase.result.json", "noncanonical Evidence artifact: formal module must be CamelCase")]),
        C(
            "uninstantiated-meta-tools",
            [],
            [W("Meta/split.py", "# pressure-gated fixture\n"), W("Meta/papergen", "pressure-gated fixture\n")],
            [D(21, "Meta/papergen", "Meta/papergen 未实例化(案号 D5-T0005)"), D(21, "Meta/split.py", "Meta/split.py 未实例化(案号 D5-T0004)")]),
        C(
            "evidence-selector-extension-collision",
            [],
            [Mirror(true, true)],
            [D(15, "Evidence/D5/S0/Carrier/Ring.result.json", "evidence selector has multiple artifact kinds: Evidence/D5/S0/Carrier/Ring.result.json, Evidence/D5/S0/Carrier/Ring.result.yaml"), D(15, "Evidence/D5/S0/Carrier/Ring.result.yaml", "evidence selector has multiple artifact kinds: Evidence/D5/S0/Carrier/Ring.result.json, Evidence/D5/S0/Carrier/Ring.result.yaml")]),
        C(
            "protected-axiom",
            [],
            [L("D5/S0/Carrier/Ring.lean", "D5/S0/Carrier/Ring", Generality.General, "namespace D5.S0.Carrier\nprotected axiom protectedBypass : False\nend D5.S0.Carrier\n")],
            [D(20, "D5/S0/Carrier/Ring.lean", "axiom declarations are confined to AxiomDebt.lean: D5.S0.Carrier.protectedBypass")]),
        C(
            "comment-only-sorry",
            [],
            [L("D5/S0/Carrier/Ring.lean", "D5/S0/Carrier/Ring", Generality.General, "-- sorry is discussion, not a term\ndef commentSafe : String := \"axiom sorry\"\n")],
            []),
        C(
            "hearts-attributed-comment-decoy",
            [L("D5/X_Frontier/Hearts.lean", "D5/X_Frontier/Hearts", Generality.Extremal, "theorem heart : True := by sorry\n")],
            [L("D5/X_Frontier/Hearts.lean", "D5/X_Frontier/Hearts", Generality.Extremal, "/-\ntheorem heart : True := by trivial\n-/\n@[simp] theorem heart : False := by sorry\n")],
            [D(8, "D5/X_Frontier/Hearts.lean", "semantic declaration identities and types are frozen")]),
        C(
            "future-theory-is-uninstantiated",
            [],
            [L("D8/S0/Carrier/Ring.lean", "D8/S0/Carrier/Ring", Generality.General, "def future : Nat := 0\n")],
            [D(21, "D8/S0/Carrier/Ring.lean", "D8 未实例化(压力未至,D5-T0009)")]),
        C(
            "valid-protected-backfill-inventory",
            [],
            [],
            []),
        C(
            "empty-protected-backfill-inventory",
            [],
            [W("Meta/BACKFILL.yaml", "schema_version: 2\ninventory: m0-protected-v1\nsources: []\n")],
            [D(16, "Meta/BACKFILL.yaml", "sources must contain at least one source")]),
        C(
            "missing-backfill-disposition",
            [],
            [Replace("        disposition: D5/S0/Carrier/Ring\n", "")],
            [D(16, "Meta/BACKFILL.yaml", "source docs/develop/theory/GICT_complete_development_v3 (3).md#GICT-heart-O5 needs a disposition")]),
        C(
            "duplicate-protected-backfill-entry",
            [],
            [Anchor("GICT-heart-O5", true)],
            [D(16, "Meta/BACKFILL.yaml", "duplicate source anchor: docs/develop/theory/GICT_complete_development_v3 (3).md#GICT-heart-O5")]),
        C(
            "dangling-backfill-entry",
            [],
            [Disposition("D5/S0/Carrier/Missing")],
            [D(16, "Meta/BACKFILL.yaml", "dangling disposition D5/S0/Carrier/Missing: canonical target is absent")]),
        C(
            "invalid-protected-backfill-schema",
            [],
            [Replace("schema_version: 2", "schema_version: 1")],
            [D(16, "Meta/BACKFILL.yaml", "BACKFILL must use schema_version 2 and inventory m0-protected-v1")]),
        C(
            "changed-protected-source-path",
            [],
            [Replace("path: \"docs/develop/theory/GICT_complete_development_v3 (3).md\"", "path: \"Library/queries.yaml\"")],
            [D(16, "Meta/BACKFILL.yaml", "source GICT-v3.6 has an invalid governance path")]),
        C(
            "ticket-target-task-mismatch",
            [],
            [Replace("  - case_id: D5-T0018\n    gid: D5/X_Frontier/BackfillTasks\n", "  - case_id: D5-T0018\n    gid: D5/S0/Carrier/Ring\n")],
            [D(16, "Meta/BACKFILL.yaml", "ticket D5-T0018 target does not declare TASK D5-T0018: D5/S0/Carrier/Ring.lean")]),
        C(
            "frontier-task-missing-ticket-index",
            [],
            [T("D5/X_Frontier/UnindexedTask.lean", "D5/X_Frontier/UnindexedTask", "D5-T0099")],
            [D(16, "Meta/BACKFILL.yaml", "frontier TASK cases are missing from ticket_index: D5-T0099")]),
        C(
            "valid-pending-query-anchor",
            [],
            [T("D5/X_Frontier/QueryTask.lean", "D5/X_Frontier/QueryTask", "D5-T0098"), W("Library/queries.yaml", "schema_version: 1\nqueries:\n  - id: D5-Q0098\n    query: fixture\n    target_gid: D5/X_Frontier/QueryTask\n    pending_case: D5-T0098\n")],
            []),
        C(
            "unresolvable-query-anchor",
            [],
            [W("Library/queries.yaml", "schema_version: 1\nqueries:\n  - id: D5-Q0099\n    query: invented paper\n    target_gid: D5/S0/Carrier/Ring\n    bibkey: invented2026result\n")],
            [D(17, "Library/queries.yaml", "query D5-Q0099 needs DOI/arXiv or a pending case")]),
        C(
            "valid-ledgered-anomaly",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"anomaly\": \"fixture drift\", \"case_id\": \"D5-T0097\"}\n")],
            []),
        C(
            "valid-typed-ledgered-anomaly",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), W("Evidence/D5/S0/Carrier/Result.run.yaml", "case_id: D5-T0097\nkind: anomaly\nstate: unresolved\n")],
            []),
    ];
}
