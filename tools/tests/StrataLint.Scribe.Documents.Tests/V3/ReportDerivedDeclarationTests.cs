using System.Collections.Immutable;
using System.Security.Cryptography;
using StrataLint.Engine;
using static StrataLint.TestSupport.ReportDerivedDeclarationFixture;

namespace StrataLint.Scribe.Tests;

public sealed class ReportDerivedDeclarationTests
{
    [Fact]
    public void Migrated_formula_documents_match_frozen_utf8_bytes_and_carry_assessed_provenance()
    {
        var definitions = DocumentAssembly.Definitions;
        var migrated = definitions
            .Single(definition => definition.Document.Header.Gid.Value ==
                "D5/S1/Depth/JointCoordinates").Document;
        var migratedDescribe = Assert.IsType<DocumentBlock.Describe>(Assert.Single(migrated.Content.Items));
        Assert.IsType<AssessedProvenance.RepoDerived>(migratedDescribe.AssessedProvenance);
        var documents = definitions.Select(static definition => definition.Document).ToArray();
        var jointDeclaration = new LeanDeclaration(
            "D5.S1.Depth.JointCoordinates.joint_coordinates_spec",
            "theorem",
            "statement-v1(source=D5.S1.Depth.JointCoordinates.joint_coordinates_spec)",
            ImmutableArray.Create("propext", "Classical.choice", "Quot.sound"));
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [JointCoordinatesLeanPath] = new(
                ImmutableArray.Create("D5.S1.Phase.Basic", "D5.S1.Scale.Log"),
                ImmutableArray.Create(jointDeclaration)),
            [GoldenDiscriminantLeanPath] = new(["D5.S0.Carrier.GoldenRatio"], [Declaration(
                "D5.S0.Carrier.GoldenDiscriminant.golden_discriminant_spec", "theorem")]),
            [GoldenRatioLeanPath] = new([], [Declaration(
                "D5.S0.Carrier.GoldenRatio.golden_ratio_spec", "theorem")]),
        });
        var catalog = DeclarationCatalog.Create(report);
        var citations = new Dictionary<string, LiteratureCitation>(StringComparer.Ordinal)
        {
            ["koshy2001fibonacci"] = LiteratureCitation.Create(
                "Thomas Koshy", 2001,
                "Fibonacci and Lucas Numbers with Applications",
                "10.1002/9781118033067"),
        };
        var graph = DocumentGraphAssembler.Assemble(
            documents,
            catalog);

        var actual = CanonicalMarkdownWriter.Write(
            migrated, catalog, graph: graph).ToArray();
        Assert.Equal(FrozenJointCoordinatesSha256, Convert.ToHexString(SHA256.HashData(actual)).ToLowerInvariant());

        AssertMigratedFormulaDocument(
            definitions, catalog, graph,
            "D5/S0/Carrier/GoldenDiscriminant", FrozenGoldenDiscriminantSha256, citations);
        AssertMigratedFormulaDocument(
            definitions, catalog, graph,
            "D5/S0/Carrier/GoldenRatio", FrozenGoldenRatioSha256, citations);
    }

    private const string JointCoordinatesLeanPath = "D5/S1/Depth/JointCoordinates.lean";
    private const string GoldenDiscriminantLeanPath = "D5/S0/Carrier/GoldenDiscriminant.lean";
    private const string GoldenRatioLeanPath = "D5/S0/Carrier/GoldenRatio.lean";
    private const string FrozenJointCoordinatesSha256 =
        "6e23be1f770de6f348478e9e57360a3abc7f33800db30634c786e00f33f2de61";
    private const string FrozenGoldenDiscriminantSha256 =
        "1ab43c115940ec373f6ea042ebb0fdfd0b6ecba3f8a3a3a306b8ff47156d4511";
    private const string FrozenGoldenRatioSha256 =
        "d4baee5d4578139d26d17f75d0b157d9873c42a7b8e2fb219b1726d7f7bc1f7f";

    private static void AssertMigratedFormulaDocument(
        IEnumerable<DocumentDefinition> definitions,
        DeclarationCatalog catalog,
        DocumentGraph graph,
        string gid,
        string expectedSha256,
        IReadOnlyDictionary<string, LiteratureCitation> citations)
    {
        var document = definitions.Single(definition => definition.Document.Header.Gid.Value == gid).Document;
        var describe = Assert.IsType<DocumentBlock.Describe>(Assert.Single(document.Content.Items));
        Assert.NotNull(describe.AssessedProvenance);
        Assert.IsType<StatementSource.Authored>(describe.StatementSource);
        var bytes = CanonicalMarkdownWriter.Write(
            document, catalog, citations: citations, graph: graph).ToArray();
        Assert.Equal(expectedSha256, Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant());
    }
}
