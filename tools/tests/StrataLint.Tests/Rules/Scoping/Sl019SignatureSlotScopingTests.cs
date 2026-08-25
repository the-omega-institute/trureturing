using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl019SignatureSlotScopingTests
{
    private const string ReceiptPath =
        "Meta/Digestion/formalizations/fixture-signature-slot.v1.json";
    private const string FailureNameKey =
        "ns(n0,35:InfiniteIdentificationFiniteFailure)";
    private const string Finding = "unknown anomaly-bearing schema";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Sl019AcceptsFailureAsMathematicalContentInAReceiptSignatureNameKey(
        bool hostedExtension)
    {
        var evaluation = Evaluate(
            ReceiptPath,
            ReceiptText(FailureNameKey, hostedExtension));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Theory]
    [InlineData("unresolved failure without case")]
    [InlineData("{\"kind\":\"failure\",\"state\":\"unresolved\"}")]
    [InlineData("FiniteFailure")]
    public void Sl019RejectsAnAnomalyRecordPlacedInAReceiptSignatureNameKey(string value)
    {
        AssertSl019Finding(Evaluate(ReceiptPath, ReceiptText(value)));
    }

    [Fact]
    public void Sl019RejectsAValidSignatureNameKeyOutsideAFormalizationReceiptPath()
    {
        const string path = "Evidence/D5/S0/Carrier/Signature.run.json";

        AssertSl019Finding(Evaluate(path, ReceiptText(FailureNameKey)));
    }

    [Fact]
    public void Sl019RejectsAValidSignatureNameKeyOutsideTheStructurallyReachedSignatureSlot()
    {
        var text = "{\"name_key\":\"" + FailureNameKey
            + "\",\"schema\":\"digestion-formalization-v1\"}\n";

        AssertSl019Finding(Evaluate(ReceiptPath, text));
    }

    [Theory]
    [InlineData("ns(n0,31:unresolved failure without case)")]
    [InlineData("ns(n0,39:{\"kind\":\"failure\",\"state\":\"unresolved\"})")]
    public void Sl019RejectsAnomalyPayloadsInsideALengthDelimitedIdentifier(string nameKey)
    {
        AssertSl019Finding(Evaluate(ReceiptPath, ReceiptText(nameKey)));
    }

    [Theory]
    [InlineData("ns(n0,31:unresolved failure without case)")]
    [InlineData("ns(n0,39:{\"kind\":\"failure\",\"state\":\"unresolved\"})")]
    public void SharedRepositoryShapeRejectsAnomalyPayloadsInsideAnIdentifier(string nameKey)
    {
        Assert.False(CanonicalLeanNameDecoder.IsRepositoryNameKey(nameKey));
    }

    [Fact]
    public void Sl019RejectsANameKeyWhoseIdentifierLengthPrefixIsNotSelfConsistent()
    {
        const string wrongLength =
            "ns(n0,34:InfiniteIdentificationFiniteFailure)";

        AssertSl019Finding(Evaluate(ReceiptPath, ReceiptText(wrongLength)));
    }

    [Fact]
    public void Sl019RejectsANameKeyWhoseIdentifierLengthCountsCharactersInsteadOfUtf8Bytes()
    {
        const string characterLength =
            "ns(n0,36:\u00e9InfiniteIdentificationFiniteFailure)";

        AssertSl019Finding(Evaluate(ReceiptPath, ReceiptText(characterLength)));
    }

    [Fact]
    public void Sl019RejectsANameKeyWhoseIdentifierLengthHasLeadingZeroes()
    {
        const string nonCanonicalLength =
            "ns(n0,035:InfiniteIdentificationFiniteFailure)";

        AssertSl019Finding(Evaluate(ReceiptPath, ReceiptText(nonCanonicalLength)));
    }

    [Fact]
    public void CurrentReceiptNameKeysSatisfyTheSharedRepositoryShape()
    {
        var root = TestRepositoryLayout.FindRoot();
        var directory = Path.Combine(root, DigestionFormalizationReceipt.RootPath);
        var nameKeys = new List<(string Path, string Value)>();
        foreach (var path in Directory.EnumerateFiles(directory, "*.v1.json"))
        {
            using var document = JsonDocument.Parse(File.ReadAllBytes(path));
            var receipt = document.RootElement;
            nameKeys.Add((
                path,
                receipt.GetProperty("precommitted_signature").GetProperty("name_key").GetString()!));
            if (!receipt.TryGetProperty("hosted_extensions", out var extensions)) continue;
            nameKeys.AddRange(extensions.EnumerateArray().Select(extension => (
                path,
                extension.GetProperty("precommitted_signature").GetProperty("name_key").GetString()!)));
        }

        Assert.NotEmpty(nameKeys);
        Assert.All(nameKeys, item => Assert.True(
            CanonicalLeanNameDecoder.IsRepositoryNameKey(item.Value),
            $"unsupported receipt name_key in {item.Path}: {item.Value}"));
    }

    private static SingleRuleEvaluation Evaluate(string path, string text)
    {
        var fixture = new RuleFixture();
        fixture.Files[path] = text;
        return RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(19),
            fixture.Build(RawChangeSet.Create([path])));
    }

    private static void AssertSl019Finding(SingleRuleEvaluation evaluation)
    {
        var findings = evaluation.Diagnostics.Where(diagnostic =>
            diagnostic.Message.Contains(Finding, StringComparison.Ordinal)
            || diagnostic.Message.Contains("unledgered anomaly", StringComparison.Ordinal));
        Assert.Single(findings);
    }

    private static string ReceiptText(string nameKey, bool hostedExtension = false)
    {
        var signature = new DigestionFormalizationSignature(
            nameKey,
            "theorem",
            "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))");
        var extensions = hostedExtension
            ? ImmutableArray.Create(new DigestionFormalizationExtension(
                "D5/S0/Carrier/SignatureSlot.secondary_probe",
                signature))
            : ImmutableArray<DigestionFormalizationExtension>.Empty;
        var receipt = new DigestionFormalizationReceipt(
            "fixture-signature-slot",
            "D5/S0/Carrier/SignatureSlot.primary_probe",
            hostedExtension
                ? new DigestionFormalizationSignature(
                    "ns(n0,13:primary_probe)",
                    "theorem",
                    "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))")
                : signature,
            "sha256:" + new string('0', 64),
            "sha256:" + new string('0', 64),
            extensions);

        return Encoding.UTF8.GetString(DigestionFormalizationReceipt.Write(receipt).AsSpan());
    }
}
