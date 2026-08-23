using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoristFrontierHistoricalRevisionReplayTests
{
    private const string Path = "D5/X_Frontier/BasePhiNegativePrefixTrident.lean";
    public static TheoryData<int> HistoricalFrontierBlobChanges => new()
        {
            9,
            10,
            11,
            12,
            13,
            14,
            16,
            17,
        };

    [Theory]
    [MemberData(nameof(HistoricalFrontierBlobChanges))]
    public void HistoricalFrontierBlobChangeRequiresARevisionDeclaration(int scene)
    {
        var fixture = TheoristFrontierHistoricalRevisionFixture.Get(scene);
        Assert.Equal(
            fixture.BaselineBlobOid,
            FrozenContentAddress.ComputeGitBlobOid(
                Encoding.UTF8.GetBytes(fixture.BaselineSource),
                HashAlgorithmName.SHA1));
        Assert.Equal(
            fixture.CandidateBlobOid,
            FrozenContentAddress.ComputeGitBlobOid(
                Encoding.UTF8.GetBytes(fixture.CandidateSource),
                HashAlgorithmName.SHA1));
        Assert.NotEqual(fixture.BaselineBlobOid, fixture.CandidateBlobOid);
        Assert.Equal(fixture.StatementSha256, ReadStatementSha(fixture.BaselineSource));
        Assert.Equal(fixture.StatementSha256, ReadStatementSha(fixture.CandidateSource));
        var changes = RawChangeSet.Create([Path]);
        var template = new RuleFixture().Build(changes);
        var baseline = WithHistoricalCarrier(
            template.Baseline,
            fixture.BaselineSource,
            fixture.BaselineBlobOid);
        var current = WithHistoricalCarrier(
            template.Current,
            fixture.CandidateSource,
            fixture.CandidateBlobOid);
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
                blobOid));
        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(decoded).Snapshot;
    }
}
