namespace StrataLint.Definitions;

internal static partial class GoldenCorpus
{
    private static GoldenCase[] Corpus3 { get; } =
    [
        C(
            "valid-typed-numeric-anomaly-with-case",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"case_id\": \"D5-T0097\", \"kind\": \"numeric-anomaly\", \"state\": \"unresolved\"}\n")],
            []),
        C(
            "typed-numeric-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"kind\": \"numeric-anomaly\", \"state\": \"unresolved\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $")]),
        C(
            "unknown-anomaly-discriminator-with-case",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"case_id\": \"D5-T0097\", \"kind\": \"anomalyish\", \"state\": \"unresolved\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unknown anomaly-bearing schema at $")]),
        C(
            "opaque-serialized-looking-string",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.json", "{\"payload\": \"{opaque machine note}\"}\n")],
            []),
        C(
            "valid-serialized-anomaly-with-case",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"prefix {\\\"case_id\\\":\\\"D5-T0097\\\",\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\\\"unresolved\\\"} suffix\"}\n")],
            []),
        C(
            "encoded-unresolved-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"{\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\\\"unresolved\\\"}\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $.payload")]),
        C(
            "prefixed-serialized-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"prefix: {\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\\\"unresolved\\\"}\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $.payload")]),
        C(
            "bom-prefixed-serialized-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"\uFEFF{\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\\\"unresolved\\\"}\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $.payload")]),
        C(
            "mid-string-serialized-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"before {\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\\\"unresolved\\\"} after\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $.payload")]),
        C(
            "malformed-anomaly-bearing-encoding",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"{\\\"kind\\\":\\\"anomaly\\\",\\\"state\\\":\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unknown anomaly-bearing schema at $.payload")]),
        C(
            "unicode-escaped-malformed-anomaly-encoding",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"payload\": \"{\\\"kind\\\":\\\"\\\\u0061nomaly\\\",\\\"state\\\":\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unknown anomaly-bearing schema at $.payload")]),
        C(
            "canonical-json-object-key-order",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.json", "{\"alpha\": 1, \"omega\": 2}\n")],
            []),
        C(
            "noncanonical-json-object-key-order",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.json", "{\"omega\": 2, \"alpha\": 1}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "object keys are not sorted at $")]),
        C(
            "canonical-yaml-object-key-order",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.yaml", "alpha: 1\nomega: 2\n")],
            []),
        C(
            "noncanonical-yaml-object-key-order",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.yaml", "omega: 2\nalpha: 1\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.yaml", "object keys are not sorted at $")]),
        C(
            "structured-artifact-file-bom",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.json", "\uFEFF{\"alpha\": 1}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "structured artifact must not start with a BOM")]),
        C(
            "structured-artifact-trailing-whitespace",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.json", "{\"alpha\": 1} \n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "structured artifact has trailing whitespace on line 1")]),
        C(
            "valid-structured-prose-ledger",
            [],
            [T("D5/X_Frontier/LedgerTask.lean", "D5/X_Frontier/LedgerTask", "D5-T0097"), W("Chronicle/2026/07/11-ledger.md", "# Round ledger\n\n<!-- STRATALINT-LEDGER\n{\"kind\":\"anomaly\",\"state\":\"unresolved\",\"case_id\":\"D5-T0097\"}\n-->\n")],
            []),
        C(
            "floating-anomaly",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"anomaly\": \"fixture drift\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $")]),
        C(
            "typed-record-anomaly-without-case",
            [],
            [WP("Evidence/D5/S0/Carrier/Result.run.json", "{", "\"kind\": \"anomaly\", \"state\": \"unresolved\"}\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.json", "unledgered anomaly at $")]),
        C(
            "yaml-block-scalar-cannot-hide-typed-anomaly",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.yaml", "records:\n  - kind: anomaly\n    note: |\n      harmless prose\n    state: unresolved\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.yaml", "unledgered anomaly at $.records[0]")]),
        C(
            "unknown-anomaly-bearing-schema",
            [],
            [W("Evidence/D5/S0/Carrier/Result.run.yaml", "resolution: pending\ntype: anomaly\n")],
            [D(19, "Evidence/D5/S0/Carrier/Result.run.yaml", "unknown anomaly-bearing schema at $")]),
        C(
            "structured-prose-ledger-anomaly-without-case",
            [],
            [W("Chronicle/2026/07/11-ledger.md", "# Round ledger\n\n<!-- STRATALINT-LEDGER\n{\"kind\":\"anomaly\",\"state\":\"unresolved\"}\n-->\n")],
            [D(19, "Chronicle/2026/07/11-ledger.md", "unledgered anomaly at ledger block 1:$")]),
        C(
            "directory-at-capacity",
            [],
            [Dir(), X("Blueprint/D5/S0/Carrier/Extra11.md")],
            []),
        C(
            "directory-over-capacity",
            [],
            [Dir()],
            [D(3, "Blueprint/D5/S0/Carrier", "directory contains 13 files (maximum 12)")]),
        C(
            "empty-mirror-waiver",
            [],
            [Waiver()],
            [D(4, RingPath, "mirror-B waiver has no reason")]),
        C(
            "exact-evidence-mirror",
            [],
            [Mirror(true, false)],
            []),
    ];
}
