using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record InformationTemplateProducerRecord(string Path, string Mode, string? Sha256);
internal sealed record InformationTemplateHistoryTarget(string Revision, string Pair, string CacheKey);
internal sealed record InformationTemplateHistoryPlan(bool Required, string ProtectedBase, string Purpose,
    string? Producer, ImmutableArray<InformationTemplateHistoryTarget> Targets)
{
    // The callback is deliberately lazy: inactive planning does not read full
    // snapshots or hash executable inputs. B owns the seed even if C retargets it.
    internal static InformationTemplateHistoryPlan Create(string revision, RepositorySnapshot baseline,
        RepositorySnapshot candidate, string purpose, Func<string> producer, string os, string arch)
    {
        InformationTemplateJson.Hash(revision, 40);
        if (purpose is not ("check" or "seed" or "discharge"))
            throw new FormatException("history purpose must be check, seed or discharge");
        var hasBase = baseline.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var baseFile);
        var hasCandidate = candidate.TryGetFile(InformationTemplateDebtStore.ActivationPath, out var candidateFile);
        var before = hasBase ? InformationTemplateDebtStore.ReadActivation(baseline) : null;
        var after = hasCandidate ? InformationTemplateDebtStore.ReadActivation(candidate) : null;
        if (purpose != "check" && (!hasBase || !hasCandidate))
            throw new FormatException("history seed/discharge requires installed activation on both sides");
        var required = hasBase && hasCandidate && (purpose != "check"
            || before!.Activated || after!.Activated
            || DeclaredTemplateBindingRule.HasRows(baseline) || DeclaredTemplateBindingRule.HasRows(candidate)
            || !baseFile!.RawBytes.AsSpan().SequenceEqual(candidateFile!.RawBytes.AsSpan()));
        if (!required) return new(false, revision, purpose, null, []);
        var address = InformationTemplateJson.Hash(producer(), 64);
        var revisions = purpose == "seed" ? new[] { before!.SeedBase } : [before!.SeedBase, revision];
        return new(true, revision, purpose, address,
            revisions.Distinct(StringComparer.Ordinal).Select(r => Target(address, r, os, arch)).ToImmutableArray());
    }

    internal static ImmutableArray<byte> ProducerBytes(IEnumerable<InformationTemplateProducerRecord> records)
    {
        var ordered = records.OrderBy(r => r.Path, StringComparer.Ordinal).ToArray();
        string? previous = null;
        foreach (var record in ordered)
        {
            if (!RepoPath.TryCreate(record.Path, out _) || record.Path.Contains('\\')
                || record.Path.Split('/').Any(p => p is "" or "." or "..") || record.Path == previous
                || record.Mode is not ("100644" or "100755" or "absent")
                || (record.Mode == "absent") != (record.Sha256 is null))
                throw new FormatException("history producer record is noncanonical: " + record.Path);
            if (record.Sha256 is not null) InformationTemplateJson.Hash(record.Sha256, 64);
            previous = record.Path;
        }
        return InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(new
        {
            schema = "information-template-history-producer-v1",
            records = ordered.Select(r => new { path = r.Path, mode = r.Mode, sha256 = r.Sha256 }),
        }));
    }

    internal static InformationTemplateHistoryTarget Target(string producer, string revision, string os, string arch)
    {
        InformationTemplateJson.Hash(producer, 64);
        InformationTemplateJson.Hash(revision, 40);
        foreach (var platform in new[] { os, arch })
            if (platform.Length == 0 || platform.Any(c => !char.IsAsciiLetterOrDigit(c) && c is not ('_' or '-')))
                throw new FormatException("history platform must be an ASCII cache-key component");
        var pair = InformationTemplateJson.Sha256(InformationTemplateJson.Canonical(JsonSerializer.SerializeToElement(new
        {
            schema = "information-template-history-pair-v1", producer, revision,
        })).AsSpan());
        return new(revision, pair, $"it-history-v1-{os}-{arch}-{producer}-{revision}");
    }
}
