using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeExtensionVerifierTests
{
    [Fact]
    public void ConservativeChangePreservesAdmitsAndEveryBlockingWitness()
    {
        var outcome = ConservativeExtensionVerifier.Verify(ConservativeTestData.Input());

        var accepted = Assert.IsType<ConservativeExtensionOutcome.Accepted>(outcome);
        var certificate = Encoding.UTF8.GetString(accepted.Certificate.AsSpan());
        Assert.Contains("\"status\": \"CORPUS_CONSERVATIVE\"", certificate, StringComparison.Ordinal);
        Assert.Contains("\"corpus_case_count\": 4", certificate, StringComparison.Ordinal);
        Assert.Contains("\"golden_case_count\": 3", certificate, StringComparison.Ordinal);
        Assert.Contains("\"replay_root\": \"sha256:", certificate, StringComparison.Ordinal);
        Assert.Contains("\"SL-022\"", certificate, StringComparison.Ordinal);
    }

    [Fact]
    public void FlippingAnOldAdmitIsAContractViolation()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.AdmitCase,
                ConservativeDisposition.Block,
                "SL-001"))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-ADMIT-FLIPPED"
                && finding.CaseId == ConservativeTestData.AdmitCase);
    }

    [Fact]
    public void RemovingAnActiveRuleBlockingWitnessIsDetectionDegradation()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-BLOCK-WITNESS-LOST"
                && finding.RuleId == "SL-001");
    }

    [Fact]
    public void AdmitDispositionCannotRetainARuleIdToFakeABlockingWitness()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit,
                "SL-001"))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-BLOCK-WITNESS-LOST"
                && finding.RuleId == "SL-001");
    }

    [Fact]
    public void MissingCandidateCaseIsInfrastructureFailure()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Where(item => item.CaseId != ConservativeTestData.RejectCase)
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("case set", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void HarnessTimeoutIsInfrastructureFailure()
    {
        var input = ConservativeTestData.Input(
            candidateExecution: new ConservativeHarnessExecution.InfrastructureFailure(
                "candidate harness timed out"));

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("timed out", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineTreeIntegrityFailureNamesTheBlockingRules()
    {
        var input = ConservativeTestData.Input() with
        {
            BaselineExecution = new ConservativeHarnessExecution.Completed(new ConservativeHarnessRun(
                "sha256:" + new string('1', 64),
                ["SL-001", "SL-022"],
                Assert.IsType<ConservativeHarnessExecution.Completed>(
                        ConservativeTestData.Input().BaselineExecution)
                    .Run.Cases
                    .Select(item => ConservativeTestData.WithDisposition(
                        item,
                        ConservativeTestData.BaseTreeCase,
                        ConservativeDisposition.Block,
                        "SL-001"))
                    .ToImmutableArray())),
        };

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("SL-001", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CertificateBytesAreStableAcrossRuns()
    {
        var input = ConservativeTestData.Input();

        var first = Assert.IsType<ConservativeExtensionOutcome.Accepted>(
            ConservativeExtensionVerifier.Verify(input));
        var second = Assert.IsType<ConservativeExtensionOutcome.Accepted>(
            ConservativeExtensionVerifier.Verify(input));

        Assert.True(first.Certificate.AsSpan().SequenceEqual(second.Certificate.AsSpan()));
    }
}
