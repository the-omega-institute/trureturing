using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class PrAMetamorphicVerifierTests
{
    [Fact]
    public void FixedMatrixRunsEveryRequiredCombinationAndPassesDeterministicProducer()
    {
        var calls = new List<PrAMatrixCase>();
        var result = PrAMetamorphicVerifier.Verify(testCase =>
        {
            calls.Add(testCase);
            return Snapshot(testCase, environmentSensitive: false);
        });

        Assert.True(result.Pass, string.Join("\n", result.Diagnostics));
        Assert.Equal(192, calls.Count);
        Assert.Equal(2, calls.Select(static item => item.OutputRoot).Distinct().Count());
        Assert.Equal(2, calls.Select(static item => item.Checkout).Distinct().Count());
        Assert.Equal(new[] { "C", "en_US.UTF-8" }, calls.Select(static item => item.Locale).Distinct().Order().ToArray());
        Assert.Equal(new[] { "Asia/Singapore", "UTC" }, calls.Select(static item => item.Timezone).Distinct().Order().ToArray());
        Assert.Equal(new[] { "canonical", "reverse", "seeded-shuffle" }, calls.Select(static item => item.Order).Distinct().Order().ToArray());
        Assert.Equal(new[] { 1, 4 }, calls.Select(static item => item.Parallelism).Distinct().Order().ToArray());
        Assert.Equal(new long[] { 0, 1 }, calls.Select(static item => item.SourceDateEpoch).Distinct().Order().ToArray());
    }

    [Fact]
    public void EnvironmentSensitiveProducerMakesTopLevelVerifierReject()
    {
        var result = PrAMetamorphicVerifier.Verify(testCase => Snapshot(testCase, environmentSensitive: true));

        Assert.False(result.Pass);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains(result.Diagnostics, static item => item.Contains("M-EMITTER-NONDETERMINISTIC", StringComparison.Ordinal));
    }

    [Fact]
    public void ClockProjectionAllowsOnlyTheSpecExcludedFieldsToChange()
    {
        var allowed = PrAMetamorphicVerifier.Verify(testCase => Snapshot(testCase, environmentSensitive: false));
        var forbidden = PrAMetamorphicVerifier.Verify(testCase =>
        {
            var snapshot = Snapshot(testCase, environmentSensitive: false);
            return testCase.SourceDateEpoch == 0
                ? snapshot
                : snapshot with { Receipt = snapshot.Receipt.Replace("\"pass\":true", "\"pass\":false", StringComparison.Ordinal) };
        });

        Assert.True(allowed.Pass);
        Assert.False(forbidden.Pass);
    }

    private static PrARunSnapshot Snapshot(PrAMatrixCase testCase, bool environmentSensitive)
    {
        var bytes = Encoding.UTF8.GetBytes(environmentSensitive ? testCase.Locale : "stable");
        var sha = Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes));
        var request = new string(testCase.SourceDateEpoch == 0 ? 'a' : 'b', 64);
        var cross = new string(testCase.SourceDateEpoch == 0 ? 'c' : 'd', 64);
        var receiptSha = new string(testCase.SourceDateEpoch == 0 ? 'e' : 'f', 64);
        var receipt = $$"""
            {"schema":"receipt-v1","request_sha256":"{{request}}","run_id":"00000000000000000000000000000000","source_tree_sha256":"{{new string('1', 64)}}","base_tree_sha256":"{{new string('2', 64)}}","producer_build_sha256":"{{new string('3', 64)}}","source_date_epoch":{{testCase.SourceDateEpoch}},"artifacts":[{"artifact_id":"A-DAG","path":"artifacts/dag.txt","sha256":"{{sha}}","mode":"100644"}],"artifact_set_sha256":"{{new string('4', 64)}}","cross_artifact_sha256":"{{cross}}","verifiers":[{"id":"byte-check","result_sha256":"{{new string('5', 64)}}","disposition":"pass"}],"pass":true}
            """;
        var handle = $$"""
            {"schema":"run-handle-v1","request_sha256":"{{request}}","run_id":"00000000000000000000000000000000","receipt_path":"receipt.json","receipt_sha256":"{{receiptSha}}"}
            """;
        return new PrARunSnapshot(
            [new PrAArtifact("A-DAG", "artifacts/dag.txt", "100644", sha, bytes.ToImmutableArray())],
            receipt,
            handle,
            ImmutableDictionary<string, ImmutableArray<byte>>.Empty.Add("byte-check", Encoding.UTF8.GetBytes("pass").ToImmutableArray()));
    }
}
