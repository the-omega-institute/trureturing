using System.Buffers.Binary;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;
using static StrataLint.TestSupport.RendererCorpusFixture;

namespace StrataLint.Scribe.Tests;


public sealed partial class FormulaCorpusInventoryTests
{
    private const string CanonicalRendererSha256 =
        "ac81e0dc33e565c52c9071161ce85666c1775b2f530b98ee74bac82a75e61f68";
    private const string UpdateCommand = "make -C tools update-renderer-contract";

    [Fact]
    public void RendererVocabularyPreservesRenderingCombinations()
    {
        var x = new Formula.Symbol(FormulaIdentifier.Create("x"));
        var y = new Formula.Symbol(FormulaIdentifier.Create("y"));
        var vocabulary = RendererVocabulary(
            FixedDocumentCorpus(),
            [new Formula.Power(new Formula.Power(x, y), new Formula.Number(2))]);

        Assert.Contains(
            "describe:kind=Theorem;provenance=RepoDerived;statement=LeanDeclaration",
            vocabulary);
        Assert.Contains(
            "formula-context:Power.Base=precedence:script;produces-script:true;starts-with-negation:false",
            vocabulary);
        Assert.Contains(
            "formula-context:Power.Exponent=precedence:atom;produces-script:false;starts-with-negation:false",
            vocabulary);
        Assert.Contains(
            "formula-children:Power(Base=Power,Exponent=Number)",
            vocabulary);
    }

    [Fact]
    public void FixedSyntheticCorpusFreezesRendererBehavior()
    {
        var fixedFormulas = FixedFormulaCorpus();
        var fixedDocuments = FixedDocumentCorpus();
        var fixedReport = LeanReportFixture.ForDocuments(fixedDocuments);
        var fixedCatalog = DeclarationCatalog.Create(fixedReport);
        var fixedGraph = DocumentGraphAssembler.Assemble(fixedDocuments, fixedCatalog);
        Assert.Empty(fixedGraph.Findings);

        using var aggregate = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var formula in fixedFormulas)
        {
            AppendLengthPrefixed(aggregate, Encoding.UTF8.GetBytes(FormulaKey(formula)));
            AppendLengthPrefixed(aggregate, Encoding.UTF8.GetBytes(LatexWriter.Write(formula)));
        }

        var citations = new Dictionary<string, LiteratureCitation>(StringComparer.Ordinal)
        {
            ["sos1957threegap"] = LiteratureCitation.Create(
                "Synthetic Author",
                2026,
                "Renderer contract fixture",
                "10.1000/renderer-contract"),
        };
        foreach (var document in fixedDocuments.OrderBy(
                     static document => document.Header.Gid.Value,
                     StringComparer.Ordinal))
        {
            AppendLengthPrefixed(
                aggregate,
                Encoding.UTF8.GetBytes(document.Header.Gid.Value));
            AppendLengthPrefixed(
                aggregate,
                CanonicalMarkdownWriter.Write(
                    document,
                    fixedCatalog,
                    citations,
                    fixedGraph).ToArray());
        }

        var actual = Convert.ToHexString(aggregate.GetHashAndReset()).ToLowerInvariant();
        if (Environment.GetEnvironmentVariable("STRATALINT_PRINT_RENDERER_CONTRACT") == "1")
        {
            throw new Xunit.Sdk.XunitException(
                $"Renderer behavior contract print mode. expected={CanonicalRendererSha256}; "
                    + $"actual={actual}; update=`{UpdateCommand}`; "
                    + $"RENDERER_CONTRACT_SHA256={actual}");
        }

        Assert.True(
            string.Equals(CanonicalRendererSha256, actual, StringComparison.Ordinal),
            $"Renderer behavior contract changed. expected={CanonicalRendererSha256}; "
                + $"actual={actual}. If intentional, run `{UpdateCommand}`.");
    }
}
