using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class FrozenPairRule
{
    internal static bool IsPairPath(string path) =>
        FrozenStatePath.IsUnderRoot(path)
        || path.StartsWith(FrozenLedgerChangeClassifier.AcceptedRoot + "/", StringComparison.Ordinal);

    internal static bool IsAffectedBy(DeltaRuleContext context) =>
        context.Changes.Paths.Any(path => IsPairPath(path.Value));

    internal static ImmutableArray<RuleFinding> Evaluate(DeltaRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var selectors = new HashSet<RepoPath>();
        var removedHashes = new Dictionary<RepoPath, HashSet<string>>();
        var currentSelectors = new HashSet<RepoPath>();
        var changedEvents = new HashSet<RepoPath>();
        foreach (var change in context.Changes.Entries.Where(change => IsPairPath(change.Path.Value)))
        {
            context.Baseline.Files.TryGetValue(change.Path, out var before);
            context.Current.Files.TryGetValue(change.Path, out var after);
            if (before is not null && after is not null
                && before.RawBytes.AsSpan().SequenceEqual(after.RawBytes.AsSpan()))
            {
                continue;
            }

            if (before is null && after is null
                || after is null && change.Kind is not RawChangeKind.Deleted)
            {
                findings.Add(Invalid(change.Path, "delta file is absent from its snapshot"));
                continue;
            }

            if (FrozenStatePath.IsUnderRoot(change.Path.Value))
            {
                if (FrozenStatePath.TryToModulePath(change.Path.Value, out var selector))
                {
                    selectors.Add(selector);
                }
                else
                {
                    findings.Add(Invalid(change.Path, "state path does not encode a canonical module"));
                }

                continue;
            }

            if (!FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            {
                findings.Add(Invalid(change.Path, "accepted event path is not canonical"));
                continue;
            }

            changedEvents.Add(change.Path);
            if (before is not null)
            {
                var previous = ReadTrustedEvent(before, findings);
                if (previous?.FreezePayload is { } payload
                    && TryAddSelector(payload.DescriptorSelector, before.Path, selectors, findings, out var selector))
                {
                    if (!removedHashes.TryGetValue(selector, out var hashes))
                    {
                        hashes = new HashSet<string>(StringComparer.Ordinal);
                        removedHashes.Add(selector, hashes);
                    }

                    hashes.Add(previous.EventHash);
                }
            }

            if (after is not null)
            {
                var load = FrozenAcceptedEventLoader.LoadFiles([after]);
                if (load is DagLedgerFilesLoadOutcome.Invalid invalid)
                {
                    findings.Add(Invalid(after.Path, invalid.Message));
                }
                else
                {
                    var accepted = ((DagLedgerFilesLoadOutcome.Loaded)load).Events.Single();
                    if (TryAddSelector(accepted.DescriptorPath.Value, after.Path, selectors, findings, out var selector))
                    {
                        currentSelectors.Add(selector);
                    }
                }
            }
        }

        // Only a new state or loss of a base Freeze can create a new broken pair (#6165).
        // A previously broken state remains outside this invariant's transition boundary.
        var atRisk = selectors.Where(selector =>
            context.Current.Files.ContainsKey(FrozenStatePath.FromModulePath(selector))
            && (!context.Baseline.Files.ContainsKey(FrozenStatePath.FromModulePath(selector))
                || removedHashes.ContainsKey(selector))).ToHashSet();
        if (atRisk.Count == 0)
        {
            return findings.ToImmutable();
        }

        // The accepted directory is an index input, not a whole-tree validation surface.
        // Trusted reads decode stored fields without deriving identities or resolving DAG edges.
        foreach (var file in context.Current.Files.Values.Where(file =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value)
            && !changedEvents.Contains(file.Path)))
        {
            var accepted = ReadTrustedEvent(file);
            if (accepted?.FreezePayload is { } payload
                && RepoPath.TryCreate(payload.DescriptorSelector, out var selector)
                && atRisk.Contains(selector))
            {
                currentSelectors.Add(selector);
            }
        }

        foreach (var selector in atRisk.OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            if (!currentSelectors.Contains(selector))
            {
                var removed = removedHashes.TryGetValue(selector, out var hashes)
                    ? $"; removed_event_hashes=[{string.Join(',', hashes.Order(StringComparer.Ordinal))}]"
                    : string.Empty;
                findings.Add(new RuleFinding(
                    FrozenStatePath.FromModulePath(selector).Value,
                    $"FROZEN_PAIR_MISSING descriptor_selector={selector.Value}: "
                    + "frozen state has no active accepted Freeze event" + removed,
                    AdmissionEffect.Block));
            }
        }

        return findings.ToImmutable();
    }

    private static bool TryAddSelector(
        string value,
        RepoPath eventPath,
        HashSet<RepoPath> selectors,
        ImmutableArray<RuleFinding>.Builder findings,
        out RepoPath selector)
    {
        if (RepoPath.TryCreate(value, out var parsed) && FrozenStatePath.IsCanonicalModulePath(parsed))
        {
            selector = parsed;
            selectors.Add(selector);
            return true;
        }

        selector = eventPath;
        findings.Add(Invalid(eventPath, $"descriptor_selector={value} is not a canonical module"));
        return false;
    }

    private static TrustedFrozenLedgerEvent? ReadTrustedEvent(
        RepositoryFile file,
        ImmutableArray<RuleFinding>.Builder? findings = null)
    {
        try
        {
            return FrozenLedgerBaseViewReader.ReadEvent(file);
        }
        catch (Exception exception) when (
            exception is JsonException or FormatException or InvalidOperationException or KeyNotFoundException)
        {
            findings?.Add(Invalid(file.Path, exception.Message));
            return null;
        }
    }

    private static RuleFinding Invalid(RepoPath path, string message) =>
        new(path.Value, "FROZEN_PAIR_INPUT_INVALID " + message, AdmissionEffect.Block);
}
