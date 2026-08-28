using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl019SignatureSlotScopingTests
{
    private const string ReceiptPath =
        "Meta/Digestion/formalizations/fixture-signature-slot.v1.json";
    private const string FailureNameKey =
        "ns(n0,35:InfiniteIdentificationFiniteFailure)";
    private const string FailureGid =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure"
        + ".lookup_copy_zero_loss_and_nonanticipating_failure";
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

    [Theory]
    [InlineData(FailureNameKey)]
    [InlineData("ns(ns(ns(n0,2:D5),2:S3),13:SignatureSlot)")]
    public void RepresentativeProducerNameKeysSatisfyTheSharedRepositoryShape(string nameKey)
    {
        // Binds the shared decoder to representative literal encodings emitted by the producer:
        // a root name and a qualified name. It turns red if decoder grammar or identifier policy
        // rejects either shape. It deliberately does not claim that every current receipt key is
        // covered; live-repository enumeration is outside this static fixture's contract.
        Assert.True(CanonicalLeanNameDecoder.IsRepositoryNameKey(nameKey));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Sl019AcceptsFailureAsMathematicalContentInAReceiptGid(bool hostedExtension)
    {
        var evaluation = Evaluate(
            ReceiptPath,
            ReceiptText(
                "ns(n0,13:primary_probe)",
                hostedExtension,
                FailureGid,
                hostedExtension
                    ? "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication"
                        + "/RetrospectiveLookupFailure.secondary_failure_probe"
                    : null));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Theory]
    [InlineData("unresolved failure without case")]
    [InlineData("{\\\"kind\\\":\\\"failure\\\",\\\"state\\\":\\\"unresolved\\\"}")]
    [InlineData("FiniteFailure")]
    [InlineData("row//failure.probe")]
    public void Sl019RejectsAnAnomalyRecordPlacedInAReceiptGid(string value)
    {
        // The canonical writer refuses these values outright, so the fixture is raw JSON: the
        // scan must reject them even when a hand-authored receipt smuggles them past the writer.
        var text = "{\"primary_gid\":\"" + value
            + "\",\"schema\":\"digestion-formalization-v1\"}\n";

        AssertSl019Finding(Evaluate(ReceiptPath, text));
    }

    [Fact]
    public void Sl019RejectsAValidGidOutsideAFormalizationReceiptPath()
    {
        const string path = "Evidence/D5/S0/Carrier/Gid.run.json";
        var text = "{\"primary_gid\":\"" + FailureGid + "\"}\n";

        AssertSl019Finding(Evaluate(path, text));
    }

    [Fact]
    public void Sl019RejectsAValidGidOutsideTheStructurallyReachedGidSlot()
    {
        var text = "{\"nested\":{\"primary_gid\":\"" + FailureGid
            + "\"},\"schema\":\"digestion-formalization-v1\"}\n";

        AssertSl019Finding(Evaluate(ReceiptPath, text));
    }

    private const string FailureBearingStatementType =
        "statement-v1(uparams=[],type=ec(ns(ns(n0,17:CommitmentVerdict),7:failure),[]))";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Sl019AcceptsFailureAsMathematicalContentInAReceiptStatementType(
        bool hostedExtension)
    {
        var evaluation = Evaluate(
            ReceiptPath,
            ReceiptText(
                "ns(n0,13:primary_probe)",
                hostedExtension,
                statementType: FailureBearingStatementType));

        Assert.Empty(evaluation.Diagnostics);
    }

    [Fact]
    public void Sl019RejectsAFailureBearingStatementTypeOutsideAFormalizationReceiptPath()
    {
        const string path = "Evidence/D5/S0/Carrier/Signature.run.json";
        var text = "{\"precommitted_signature\":{\"kind\":\"theorem\",\"name_key\":\"k\","
            + "\"type\":\"" + FailureBearingStatementType + "\"}}\n";

        AssertSl019Finding(Evaluate(path, text));
    }

    [Fact]
    public void Sl019RejectsAnAnomalyProseValuePlacedInAReceiptStatementType()
    {
        AssertSl019Finding(Evaluate(
            ReceiptPath,
            ReceiptText(
                "ns(n0,13:primary_probe)",
                statementType: "unresolved failure without case")));
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

    private static string ReceiptText(
        string nameKey,
        bool hostedExtension = false,
        string? primaryGid = null,
        string? extensionGid = null,
        string? statementType = null)
    {
        var signature = new DigestionFormalizationSignature(
            nameKey,
            "theorem",
            statementType ?? "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))");
        var extensions = hostedExtension
            ? ImmutableArray.Create(new DigestionFormalizationExtension(
                extensionGid ?? "D5/S0/Carrier/SignatureSlot.secondary_probe",
                signature))
            : ImmutableArray<DigestionFormalizationExtension>.Empty;
        var receipt = new DigestionFormalizationReceipt(
            "fixture-signature-slot",
            primaryGid ?? "D5/S0/Carrier/SignatureSlot.primary_probe",
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
