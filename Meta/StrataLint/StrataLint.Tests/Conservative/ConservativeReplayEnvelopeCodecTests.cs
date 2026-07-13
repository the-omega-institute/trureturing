using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeReplayEnvelopeCodecTests
{
    [Fact]
    public void CanonicalEnvelopeRoundTripsAllBaseOwnedInputs()
    {
        var corpus = new MaterializedConservativeCorpus(
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("{}\n")),
            GoldenCorpusMaterializer.ContentRoot(Encoding.UTF8.GetBytes("{}\n")),
            ["golden:fixture"]);
        var baseline = new ConservativeRepositoryIdentity(new string('a', 40), "git-sha1:" + new string('b', 40));
        var candidate = new ConservativeRepositoryIdentity(new string('c', 40), "git-sha1:" + new string('d', 40));

        var materialized = ConservativeReplayEnvelopeCodec.Create(
            corpus,
            baseline,
            candidate,
            Encoding.UTF8.GetBytes("baseline-report\n"),
            Encoding.UTF8.GetBytes("candidate-report\n"),
            Encoding.UTF8.GetBytes("git-bundle\n"));
        var decoded = ConservativeReplayEnvelopeCodec.Read(materialized.CanonicalBytes.AsSpan());

        Assert.Equal(materialized.Root, decoded.Root);
        Assert.Equal(corpus.Root, decoded.Corpus.Root);
        Assert.Equal(corpus.CaseIds.ToArray(), decoded.Corpus.CaseIds.ToArray());
        Assert.Equal(baseline, decoded.BaselineIdentity);
        Assert.Equal(candidate, decoded.CandidateIdentity);
        Assert.Equal("baseline-report\n", Encoding.UTF8.GetString(decoded.BaselineLeanReport.AsSpan()));
        Assert.Equal("candidate-report\n", Encoding.UTF8.GetString(decoded.CandidateLeanReport.AsSpan()));
        Assert.Equal("git-bundle\n", Encoding.UTF8.GetString(decoded.RepositoryBundle.AsSpan()));
    }

    [Fact]
    public void NoncanonicalEnvelopeFailsClosed()
    {
        var corpusBytes = Encoding.UTF8.GetBytes("{}\n");
        var materialized = ConservativeReplayEnvelopeCodec.Create(
            new MaterializedConservativeCorpus(
                ImmutableArray.CreateRange(corpusBytes),
                GoldenCorpusMaterializer.ContentRoot(corpusBytes),
                ["golden:fixture"]),
            new ConservativeRepositoryIdentity(new string('a', 40), "git-sha1:" + new string('b', 40)),
            new ConservativeRepositoryIdentity(new string('c', 40), "git-sha1:" + new string('d', 40)),
            [1],
            [2],
            [3]);
        var padded = materialized.CanonicalBytes.Insert(0, (byte)' ');

        var exception = Assert.Throws<FormatException>(() =>
            ConservativeReplayEnvelopeCodec.Read(padded.AsSpan()));

        Assert.Contains("canonical", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReplayRootIgnoresNoncanonicalGitPackEncoding()
    {
        var corpusBytes = Encoding.UTF8.GetBytes("{}\n");
        var corpus = new MaterializedConservativeCorpus(
            ImmutableArray.CreateRange(corpusBytes),
            GoldenCorpusMaterializer.ContentRoot(corpusBytes),
            ["golden:fixture"]);
        var baseline = new ConservativeRepositoryIdentity(
            new string('a', 40),
            "git-sha1:" + new string('b', 40));
        var candidate = new ConservativeRepositoryIdentity(
            new string('c', 40),
            "git-sha1:" + new string('d', 40));

        var first = ConservativeReplayEnvelopeCodec.Create(
            corpus,
            baseline,
            candidate,
            [1],
            [2],
            Encoding.UTF8.GetBytes("pack encoding one\n"));
        var second = ConservativeReplayEnvelopeCodec.Create(
            corpus,
            baseline,
            candidate,
            [1],
            [2],
            Encoding.UTF8.GetBytes("different pack encoding\n"));

        Assert.NotEqual(first.CanonicalBytes.ToArray(), second.CanonicalBytes.ToArray());
        Assert.Equal(first.Root, second.Root);
    }
}
