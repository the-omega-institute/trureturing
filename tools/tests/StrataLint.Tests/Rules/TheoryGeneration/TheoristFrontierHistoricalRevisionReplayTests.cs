using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoristFrontierHistoricalRevisionReplayTests
{
    private const string Path = "D5/X_Frontier/BasePhiNegativePrefixTrident.lean";
    private const string StatementSha =
        "sha256:25ddd0972fd7b97c88f87ea47bb9843e5c014cdad5344c37451293f18cb4a0d9";

    public static TheoryData<int, string, string, string, string, string, string>
        HistoricalFrontierBlobChanges => new()
        {
            {
                9,
                "54fe11737c9d83a0794121b66c41a3c01b25f1be",
                "e5dc4e2eb0ad90dead00dcaaa18871653857abe9",
                "7c7a8509e8a07b330795341f125ed99078d0afd7",
                "379c55a672797dd8210c00f5d13e7caf072dcd04",
                StatementSha,
                StatementSha
            },
            {
                10,
                "e5dc4e2eb0ad90dead00dcaaa18871653857abe9",
                "8b82f2c4f15336438711376dd1f35864c52ecfae",
                "379c55a672797dd8210c00f5d13e7caf072dcd04",
                "c868750e57b77c27c1728eeb572671e19a194936",
                StatementSha,
                StatementSha
            },
            {
                11,
                "8b82f2c4f15336438711376dd1f35864c52ecfae",
                "da1cc8656013946dbace193eb6469190fb66e664",
                "c868750e57b77c27c1728eeb572671e19a194936",
                "7967fb65511ca6c35304b0a452035ba1a6af3afc",
                StatementSha,
                StatementSha
            },
            {
                12,
                "da1cc8656013946dbace193eb6469190fb66e664",
                "56cb98317af755c099b40c983a15f98b53b9095a",
                "7967fb65511ca6c35304b0a452035ba1a6af3afc",
                "d8047bf63b6451acfeab713787c27da88b51d2aa",
                StatementSha,
                StatementSha
            },
            {
                13,
                "56cb98317af755c099b40c983a15f98b53b9095a",
                "17375d3b099ce76ce6b7faad760d131ee987cdf2",
                "d8047bf63b6451acfeab713787c27da88b51d2aa",
                "de84b99fe75184145afa1e537cba253de7100777",
                StatementSha,
                StatementSha
            },
            {
                14,
                "17375d3b099ce76ce6b7faad760d131ee987cdf2",
                "3562a9aa8de78ae4b54d52674666bd2bd77d5e59",
                "de84b99fe75184145afa1e537cba253de7100777",
                "b2b7e0d77e80fc603d0eaaa77c66fc383dd8ce79",
                StatementSha,
                StatementSha
            },
            {
                16,
                "84162846de144032a5f4bd3637e757cdc2378ca0",
                "b4a185b82388a060c3bc9d9e8e64ece3ad1e32f1",
                "b2b7e0d77e80fc603d0eaaa77c66fc383dd8ce79",
                "d44ceefa8219b743f9018aa3d9335cde956e5cee",
                StatementSha,
                StatementSha
            },
            {
                17,
                "b4a185b82388a060c3bc9d9e8e64ece3ad1e32f1",
                "f86dd2ba372fca7d90047caf6d35ac11cadcca5f",
                "d44ceefa8219b743f9018aa3d9335cde956e5cee",
                "cc57e467892a7705d26959d3941756c621f81b58",
                StatementSha,
                StatementSha
            },
        };

    [Theory]
    [MemberData(nameof(HistoricalFrontierBlobChanges))]
    public void HistoricalFrontierBlobChangeRequiresARevisionDeclaration(
        int scene,
        string baselineCommit,
        string candidateCommit,
        string baselineBlob,
        string candidateBlob,
        string baselineStatement,
        string candidateStatement)
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        Assert.Equal(
            baselineBlob,
            ReviewRegressionTests.RunGit(
                repositoryRoot,
                "rev-parse",
                $"{baselineCommit}:{Path}").Trim());
        Assert.Equal(
            candidateBlob,
            ReviewRegressionTests.RunGit(
                repositoryRoot,
                "rev-parse",
                $"{candidateCommit}:{Path}").Trim());
        Assert.NotEqual(baselineBlob, candidateBlob);
        Assert.Equal(baselineStatement, candidateStatement);

        var baselineSource = ReviewRegressionTests.RunGit(
            repositoryRoot,
            "cat-file",
            "blob",
            baselineBlob);
        var candidateSource = ReviewRegressionTests.RunGit(
            repositoryRoot,
            "cat-file",
            "blob",
            candidateBlob);
        Assert.Equal(baselineStatement, ReadStatementSha(baselineSource));
        Assert.Equal(candidateStatement, ReadStatementSha(candidateSource));
        var changes = RawChangeSet.Create([Path]);
        var template = new RuleFixture().Build(changes);
        var baseline = WithHistoricalCarrier(template.Baseline, baselineSource, baselineBlob);
        var current = WithHistoricalCarrier(template.Current, candidateSource, candidateBlob);
        var context = RuleEvaluationContext.Create(
            current,
            baseline,
            template.Policy,
            template.Lean,
            changes,
            template.MetaEvaluation,
            template.VerifiedScribeEmissions,
            baseline);

        Assert.True(
            TheoristFrontierContractValidator.IsDeliveryIdentityAffected(context),
            $"historical scene {scene} must execute SL-027");
        var diagnostic = Assert.Single(
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(27), context).Diagnostics);
        Assert.Equal(Path, diagnostic.Path);
        Assert.Contains(
            "changed Frontier module blob requires a revision declaration",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.True(scene is >= 9 and <= 17);
    }

    private static string ReadStatementSha(string source)
    {
        var start = source.IndexOf(
            TheoristFrontierContractValidator.Marker,
            StringComparison.Ordinal);
        Assert.True(start >= 0);
        start += TheoristFrontierContractValidator.Marker.Length;
        var end = source.IndexOf("\n-/", start, StringComparison.Ordinal);
        Assert.True(end >= 0);
        using var document = JsonDocument.Parse(source[start..end]);
        return Assert.IsType<string>(document.RootElement
            .GetProperty("exact_statement")
            .GetProperty("statement_sha256")
            .GetString());
    }

    private static RepositorySnapshot WithHistoricalCarrier(
        RepositorySnapshot snapshot,
        string source,
        string blobOid)
    {
        var entries = snapshot.Files.Values
            .Where(static file => file.Path.Value != Path)
            .Select(static file => new RawRepositoryEntry(
                file.Path.Value,
                file.RawBytes,
                file.GitBlobOid))
            .Append(new RawRepositoryEntry(
                Path,
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(source)),
                "git-sha1:" + blobOid));
        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
    }
}
