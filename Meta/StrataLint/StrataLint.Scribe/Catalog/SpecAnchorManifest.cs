using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class SpecAnchorManifest
{
    private const string SpecPath = "docs/develop/spec/golden-ledger-repo-spec.md";
    private const string SpecHash = "c1e74218ce9b7c78413b66fb067a3cff0d9ed9c280c4d203812e116355274884";

    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        Spec(AnchorCatalogDefinitions.SpecA1, "A1", "**A1 理论码**"),
        Spec(AnchorCatalogDefinitions.SpecA11, "A11", "**A11 论文码**"),
        Spec(AnchorCatalogDefinitions.SpecSl002, "SL-002", "| H2 |", "SL-002"),
        Spec(AnchorCatalogDefinitions.SpecSl003, "SL-003", "| H3 |", "SL-003"),
        Spec(AnchorCatalogDefinitions.SpecSl014, "SL-014", "**A14 版本码**", "SL-014"),
        Spec(AnchorCatalogDefinitions.SpecSl016, "SL-016", "`Meta/BACKFILL.yaml`:", "SL-016"),
        Spec(AnchorCatalogDefinitions.SpecSl017, "SL-017", "**锚可解析律**(SL-017):"),
        Spec(AnchorCatalogDefinitions.SpecSl018, "SL-018", "**值出机器律**(SL-018):"),
        Spec(AnchorCatalogDefinitions.SpecSl019, "SL-019", "## 11.25 落账律", "SL-019"),
        Spec(
            AnchorCatalogDefinitions.SpecByteCanonicalization,
            "byte-canonicalization",
            "**A2 全域标识符 GID",
            "受 manifest 路由"),
        Spec(AnchorCatalogDefinitions.SpecHumanGates, "human-gates", "## 1.5 人类门控"),
        Spec(AnchorCatalogDefinitions.SpecSample11, "sample-11", "**样例 11|论文配方"),
    ];

    private static AnchorDefinition Spec(
        SpecAnchor anchor,
        string clause,
        string linePrefix,
        string? token = null) =>
        new(
            anchor,
            new SpecClauseTarget(
                "spec:v7.11:" + clause,
                SpecPath,
                "v7.11",
                SpecHash,
                new StructuralSelector(linePrefix, token)),
            AnchorRegistrationStatus.Resolved);
}
