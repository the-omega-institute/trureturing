using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class TheoryAnchorManifest
{
    private const string GictPath = "docs/develop/theory/GICT_complete_development_v3 (3).md";
    private const string GictHash = "d61cda25af5f6bf17b065711ee762b63d6d196f94dd77e5ece962cf146bc163c";
    private const string PzgPath = "docs/develop/theory/PZG_BEDC_kernel_formal_170.md";
    private const string PzgHash = "02f17b403914c50795a82e54658061920b5510cb83ee9ce9587134e500060279";

    internal static AnchorDefinition GictI1Definition1_1 { get; } = Gict(
        AnchorCatalogDefinitions.GictI1Definition1_1,
        "I.1:definition:1.1",
        "**定义 1.1**");

    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        GictI1Definition1_1,
        Gict(AnchorCatalogDefinitions.GictI1Definition1_2, "I.1:definition:1.2", "**定义 1.2**"),
        Gict(AnchorCatalogDefinitions.GictI2Definition1_4, "I.2:definition:1.4", "**定义 1.4(三轴)**"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3I, "I.1:theorem:1.3:i", "**定理 1.3**", "(i)"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3II, "I.1:theorem:1.3:ii", "**定理 1.3**", "(ii)"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3III, "I.1:theorem:1.3:iii", "**定理 1.3**", "(iii)"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3IV, "I.1:theorem:1.3:iv", "**定理 1.3**", "(iv)"),
        Gict(AnchorCatalogDefinitions.GictVIIIHearts, "VIII:section:hearts", "# 第 VIII 卷:开放问题与两颗心脏"),
        Gict(AnchorCatalogDefinitions.GictAppendixA, "appendix:A", "## 附录 A:常数总表"),
        Pzg(AnchorCatalogDefinitions.Pzg6_18, "6.18", "**评注 6.18("),
        Pzg(AnchorCatalogDefinitions.Pzg6_19, "6.19", "**命题 6.19("),
        Pzg(AnchorCatalogDefinitions.Pzg26_3, "26.3", "**定理 26.3("),
        Pzg(AnchorCatalogDefinitions.Pzg26_4, "26.4", "**账目 26.4("),
    ];

    private static AnchorDefinition Gict(
        GictAnchor anchor,
        string semanticSuffix,
        string linePrefix,
        string? token = null) =>
        new(
            anchor,
            new TheoryNodeTarget(
                "gict:v3.6:" + semanticSuffix,
                "GICT-v3.6",
                GictPath,
                "v3.6",
                GictHash,
                new StructuralSelector(linePrefix, token, HeadingPrefix(anchor))),
            AnchorRegistrationStatus.Resolved);

    private static AnchorDefinition Pzg(
        PzgAnchor anchor,
        string entry,
        string linePrefix) =>
        new(
            anchor,
            new TheoryNodeTarget(
                "pzg:v170:" + entry,
                "PZG-v170",
                PzgPath,
                "v170",
                PzgHash,
                new StructuralSelector(linePrefix)),
            AnchorRegistrationStatus.Resolved);

    internal static string HeadingPrefix(GictAnchor anchor)
    {
        if (anchor.Kind is TheoryNodeKind.Appendix)
        {
            return "## 附录 " + anchor.Label.Value + ":";
        }

        var division = anchor.Division
            ?? throw new InvalidOperationException("Non-appendix GICT anchors require a division.");
        return division.Value.Contains('.')
            ? "## " + division.Value + " "
            : "# 第 " + division.Value + " 卷:";
    }
}
