using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record ConservativeReplayEnvelope(
    ImmutableArray<byte> CanonicalBytes,
    string Root,
    MaterializedConservativeCorpus Corpus,
    ConservativeRepositoryIdentity BaselineIdentity,
    ConservativeRepositoryIdentity CandidateIdentity,
    ImmutableArray<byte> BaselineLeanReport,
    ImmutableArray<byte> CandidateLeanReport,
    ImmutableArray<byte> RepositoryBundle);

internal static class ConservativeReplayEnvelopeCodec
{
    private const string Schema = "stratalint-conservative-replay-v1";

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        PropertyNameCaseInsensitive = false,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
    };

    internal static ConservativeReplayEnvelope Create(
        MaterializedConservativeCorpus corpus,
        ConservativeRepositoryIdentity baselineIdentity,
        ConservativeRepositoryIdentity candidateIdentity,
        ReadOnlySpan<byte> baselineLeanReport,
        ReadOnlySpan<byte> candidateLeanReport,
        ReadOnlySpan<byte> repositoryBundle)
    {
        ArgumentNullException.ThrowIfNull(corpus);
        ArgumentNullException.ThrowIfNull(baselineIdentity);
        ArgumentNullException.ThrowIfNull(candidateIdentity);
        var material = JsonSerializer.SerializeToElement(new
        {
            baseline = new
            {
                commit_oid = baselineIdentity.CommitOid,
                lean_report_base64 = Convert.ToBase64String(baselineLeanReport),
                tree_oid = baselineIdentity.TreeOid,
            },
            candidate = new
            {
                commit_oid = candidateIdentity.CommitOid,
                lean_report_base64 = Convert.ToBase64String(candidateLeanReport),
                tree_oid = candidateIdentity.TreeOid,
            },
            corpus_base64 = Convert.ToBase64String(corpus.CanonicalBytes.AsSpan()),
            corpus_case_ids = corpus.CaseIds,
            corpus_root = corpus.Root,
            repository_bundle_base64 = Convert.ToBase64String(repositoryBundle),
            schema = Schema,
        });
        return Read(StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }

    internal static ConservativeReplayEnvelope Read(ReadOnlySpan<byte> bytes)
    {
        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException("conservative replay envelope must be strict UTF-8", exception);
        }

        ImmutableArray<byte> canonical;
        try
        {
            canonical = StructuredCanonicalWriter.WriteJson(text);
        }
        catch (JsonException exception)
        {
            throw new FormatException("conservative replay envelope is not valid JSON", exception);
        }

        if (!canonical.AsSpan().SequenceEqual(bytes))
        {
            throw new FormatException("conservative replay envelope bytes are not canonical JSON");
        }

        ReplayDocument document;
        try
        {
            document = JsonSerializer.Deserialize<ReplayDocument>(text, JsonOptions)
                ?? throw new FormatException("conservative replay envelope is null");
        }
        catch (JsonException exception)
        {
            throw new FormatException("conservative replay envelope schema is invalid", exception);
        }

        if (!string.Equals(document.Schema, Schema, StringComparison.Ordinal)
            || document.CorpusCaseIds.IsDefaultOrEmpty)
        {
            throw new FormatException("conservative replay envelope required fields are missing");
        }

        RequireSortedUnique(document.CorpusCaseIds);
        var corpusBytes = Decode(document.CorpusBase64, "corpus");
        var baselineReport = Decode(document.Baseline.LeanReportBase64, "baseline Lean report");
        var candidateReport = Decode(document.Candidate.LeanReportBase64, "candidate Lean report");
        var bundle = Decode(document.RepositoryBundleBase64, "repository bundle");
        if (baselineReport.IsEmpty || candidateReport.IsEmpty || bundle.IsEmpty)
        {
            throw new FormatException("conservative replay envelope contains an empty required object");
        }

        var actualCorpusRoot = GoldenCorpusMaterializer.ContentRoot(corpusBytes.AsSpan());
        if (!string.Equals(actualCorpusRoot, document.CorpusRoot, StringComparison.Ordinal))
        {
            throw new FormatException("conservative replay corpus root does not match its bytes");
        }

        var baselineIdentity = Identity(document.Baseline, "baseline");
        var candidateIdentity = Identity(document.Candidate, "candidate");
        var replayRootMaterial = JsonSerializer.SerializeToElement(new
        {
            baseline = new
            {
                commit_oid = baselineIdentity.CommitOid,
                lean_report_root = GoldenCorpusMaterializer.ContentRoot(
                    baselineReport.AsSpan()),
                tree_oid = baselineIdentity.TreeOid,
            },
            candidate = new
            {
                commit_oid = candidateIdentity.CommitOid,
                lean_report_root = GoldenCorpusMaterializer.ContentRoot(
                    candidateReport.AsSpan()),
                tree_oid = candidateIdentity.TreeOid,
            },
            corpus_case_ids = document.CorpusCaseIds,
            corpus_root = actualCorpusRoot,
            schema = "stratalint-conservative-replay-root-v1",
        });
        var replayRootBytes = StructuredCanonicalWriter.WriteJson(replayRootMaterial);
        return new ConservativeReplayEnvelope(
            canonical,
            GoldenCorpusMaterializer.ContentRoot(replayRootBytes.AsSpan()),
            new MaterializedConservativeCorpus(
                corpusBytes,
                actualCorpusRoot,
                document.CorpusCaseIds),
            baselineIdentity,
            candidateIdentity,
            baselineReport,
            candidateReport,
            bundle);
    }

    private static ConservativeRepositoryIdentity Identity(ReplaySide side, string label)
    {
        if (side.CommitOid.Length is not (40 or 64)
            || side.CommitOid.Any(static value => !char.IsAsciiHexDigit(value)))
        {
            throw new FormatException($"conservative replay {label} commit OID is invalid");
        }

        var prefix = side.CommitOid.Length == 40 ? "git-sha1:" : "git-sha256:";
        var tree = side.TreeOid.StartsWith(prefix, StringComparison.Ordinal)
            ? side.TreeOid[prefix.Length..]
            : string.Empty;
        if (tree.Length != side.CommitOid.Length
            || tree.Any(static value => !char.IsAsciiHexDigit(value)))
        {
            throw new FormatException($"conservative replay {label} tree OID is invalid");
        }

        return new ConservativeRepositoryIdentity(side.CommitOid, side.TreeOid);
    }

    private static ImmutableArray<byte> Decode(string encoded, string label)
    {
        try
        {
            return ImmutableArray.CreateRange(Convert.FromBase64String(encoded));
        }
        catch (FormatException exception)
        {
            throw new FormatException($"conservative replay {label} is not base64", exception);
        }
    }

    private static void RequireSortedUnique(ImmutableArray<string> values)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (string.IsNullOrWhiteSpace(value)
                || previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException(
                    "conservative replay corpus case ids must be sorted and unique");
            }

            previous = value;
        }
    }

    private sealed record ReplayDocument(
        string Schema,
        ReplaySide Baseline,
        ReplaySide Candidate,
        string CorpusBase64,
        string CorpusRoot,
        ImmutableArray<string> CorpusCaseIds,
        string RepositoryBundleBase64);

    private sealed record ReplaySide(
        string CommitOid,
        string TreeOid,
        string LeanReportBase64);
}
