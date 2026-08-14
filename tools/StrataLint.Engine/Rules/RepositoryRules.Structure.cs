using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    internal const string HeartsPath = "D5/X_Frontier/Hearts.lean";

    private static ImmutableArray<RuleFinding> Imports(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files.OrderBy(item => item.Key.Value, StringComparer.Ordinal))
        {
            foreach (var module in report.Imports.Where(static item => item.StartsWith("D5.", StringComparison.Ordinal)))
            {
                var target = module.Replace('.', '/') + ".lean";
                if (!context.Current.TryGetFile(target, out _))
                {
                    findings.Add(new RuleFinding(path.Value, $"managed import {target} does not exist"));
                }
                else if (!ImportAllowed(path.Value, target))
                {
                    findings.Add(new RuleFinding(path.Value, $"stratum closure may not import {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Sorry(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, report) in context.Lean.Report.Files)
        {
            var declarations = report.Declarations
                .Where(static item => item.Axioms.Contains("sorryAx", StringComparer.Ordinal))
                .Select(static item => item.Name)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (declarations.Length > 0 && !path.Value.Contains("/X_Frontier/", StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    "sorryAx occurs in declaration closure: " + string.Join(", ", declarations)));
            }
        }

        return findings.ToImmutable();
    }

    // SL-003 capacity limits. These are the single enforcement source shared by
    // the admission rule (Capacity, below) and the ArchitectureTests CapacityPolicy
    // dotnet-test net, so both agree on the exact thresholds with no drift.
    internal const int ArtifactHardLineLimit = 800;

    internal const int ArtifactSoftLineLimit = 600;

    internal const int DirectoryFileLimit = 12;

    // The repository-wide capacity net tolerates a band above the admission limit.
    // Capacity is pressure, not correctness: an overfull bucket is a signal to split
    // (CLAUDE.md 8), and by the tiers of 20 a reversible content-level fact belongs in
    // detect-and-correct. Without the band, two PRs branched from the same base can each
    // add one file to a bucket holding eleven, each see twelve and admit, and their union
    // of thirteen turns the repository-wide scan red - blocking every unrelated PR until
    // someone splits. That is what made strict (now forbidden, 19) load-bearing. The
    // admission rule keeps the unbanded limit, so the next change touching that bucket is
    // still refused and the split pressure lands exactly where it belongs.
    internal const int DirectoryToleranceLimit = 24;

    // SL-003 capacity exclusions: theory inputs, the Lake manifest, the backfill
    // inventory, atomizer dialect registry, canonical CAS blobs, per-atom
    // formalization receipts, and emitted Blueprint projections are not artifacts
    // the capacity pressure rule bounds. Machine inventories grow one entry per
    // admitted unit and are never navigated as content buckets; the atomizer registry
    // is one canonical strict-loader input, not a content artifact to split. A
    // Blueprint document's structural slot is its .scribe.cs source (FILEMAP
    // kind=generated for the .md, produced by ScribeEmitter and verified by
    // its producer); its GID must name an existing Lean module and the definition path
    // is bijective with that GID, so bounding the projections would cap a lawful
    // twelve-module Lean bucket at six blueprinted modules. Single source shared with
    // the CapacityPolicy dotnet-test net.
    internal static bool IsCapacityExcluded(string path) =>
        path.StartsWith("docs/develop/", StringComparison.Ordinal)
        || string.Equals(path, "lake-manifest.json", StringComparison.Ordinal)
        || string.Equals(path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
        || path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
        || string.Equals(path, TheoryAtomizerDataLoader.DataPath, StringComparison.Ordinal)
        || DigestionCasStore.IsCanonicalPath(path)
        || FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
        || path.StartsWith(DigestionFormalizationReceipt.RootPath, StringComparison.Ordinal)
        || path.StartsWith(DigestionFidelityAttestation.RootPath, StringComparison.Ordinal)
        || (path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".md", StringComparison.Ordinal));

    // The canonical artifact line count: newline-delimited lines, not counting a
    // trailing terminator. Shared with CapacityPolicy so both nets agree exactly.
    internal static int CountArtifactLines(string text) =>
        text.Split('\n').Length - (text.EndsWith('\n') ? 1 : 0);

    private static ImmutableArray<RuleFinding> Capacity(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in context.Current.Files)
        {
            if (IsCapacityExcluded(path.Value))
            {
                continue;
            }

            var lineCount = CountArtifactLines(file.Text);
            if (lineCount > ArtifactHardLineLimit)
            {
                findings.Add(new RuleFinding(path.Value, "artifact exceeds 800 lines"));
            }
            else if (lineCount > ArtifactSoftLineLimit)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"artifact spans {lineCount} lines (soft limit {ArtifactSoftLineLimit}, "
                    + $"hard limit {ArtifactHardLineLimit})",
                    AdmissionEffect.Observe));
            }

            var directory = DirectoryOf(path.Value);
            directories[directory] = directories.GetValueOrDefault(directory) + 1;
        }

        // Occupancy is counted over the whole tree so the number reported is the real one, but
        // only buckets this change touches are reported. DirectoryToleranceLimit above was added
        // so that a union of two independently-admitted PRs would not end up "blocking every
        // unrelated PR until someone splits" - and it was wired into the repository-wide net
        // alone, leaving this rule scanning every directory and blocking them anyway. On
        // 2026-08-13 that is exactly what happened: two deposits branched from an eleven-file
        // D5/S3/Constants each saw twelve and admitted, and the union of thirteen stopped dev
        // and every unrelated branch. Every member of that bucket is frozen, so it cannot be
        // split by moving anything; the block had no exit. Scoping is what the comment above
        // already claims this rule does - the next change *touching that bucket* is still
        // refused, and the split pressure lands exactly where it belongs.
        var touched = context.Changes.Paths
            .Select(static path => DirectoryOf(path.Value))
            .ToHashSet(StringComparer.Ordinal);
        findings.AddRange(directories
            .Where(static item => item.Value > DirectoryToleranceLimit)
            .Select(static item => new RuleFinding(
                item.Key,
                $"directory contains {item.Value} files (repository tolerance "
                + $"{DirectoryToleranceLimit}; split per CLAUDE.md 8)")));
        findings.AddRange(directories
            .Where(item => item.Value > DirectoryFileLimit
                && item.Value <= DirectoryToleranceLimit
                && touched.Contains(item.Key))
            .Select(static item => new RuleFinding(
                item.Key,
                $"directory contains {item.Value} files (admission limit "
                + $"{DirectoryFileLimit}, repository tolerance "
                + $"{DirectoryToleranceLimit}; split per CLAUDE.md 8)")));
        return findings.ToImmutable();
    }

    private static string DirectoryOf(string path)
    {
        var slash = path.LastIndexOf('/');
        return slash < 0 ? "." : path[..slash];
    }

    private static ImmutableArray<RuleFinding> Mirrors(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                continue;
            }

            ValidateMirror(path.Value, "mirror-B", header.MirrorB, "D5/B/", context.Current, findings);
            ValidateMirror(path.Value, "mirror-E", header.MirrorE, "D5/E/", context.Current, findings);
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Chronicle(RuleEvaluationContext context) =>
        context.ForkPoint.Files
            .Where(static item => item.Key.Value.StartsWith("Chronicle/", StringComparison.Ordinal))
            .Where(item => !context.Current.TryGetFile(item.Key.Value, out var current)
                || !current.RawBytes.AsSpan().SequenceEqual(item.Value.RawBytes.AsSpan()))
            .Select(static item => new RuleFinding(item.Key.Value, "tracked Chronicle entries are append-only"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Badges(RuleEvaluationContext context) =>
        context.Current.Files
            .Where(static item => IsStatusScope(item.Key.Value) && BadgePattern.IsMatch(item.Value.Text))
            .Select(static item => new RuleFinding(item.Key.Value, "hand-written status badge is forbidden"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Hearts(RuleEvaluationContext context)
    {
        try
        {
            if (context.Current.TryGetFile(HeartsAuthorizationLedger.Path, out var authorizationFile))
            {
                _ = HeartsAuthorizationLedger.Read(authorizationFile.Text);
            }
        }
        catch (FormatException exception)
        {
            return ImmutableArray.Create(
                new RuleFinding(HeartsAuthorizationLedger.Path, exception.Message));
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var change in context.Changes.Entries)
        {
            if (change.Path.Value == HeartsPath
                && change.Kind is RawChangeKind.Modified or RawChangeKind.Deleted)
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    "Hearts.lean is immutable; change SL-008 in the same changeset and pass the "
                    + "SL-022 protected-surface gate"));
            }

            if (FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value)
                && change.Kind is RawChangeKind.Modified or RawChangeKind.Deleted)
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    "accepted frozen-ledger event files are append-only; run ledger-reattest to "
                    + "add a new event and do not modify an already-frozen fragment"));
            }
        }

        var acceptedFiles = context.Current.Files
            .Where(static item => FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value))
            .Select(static item => item.Value)
            .ToImmutableArray();
        var loadOutcome = FrozenAcceptedEventLoader.LoadFiles(acceptedFiles);
        if (loadOutcome is DagLedgerFilesLoadOutcome.Invalid invalid)
        {
            findings.Add(new RuleFinding(
                FrozenLedgerChangeClassifier.AcceptedRoot,
                "candidate frozen ledger is invalid: " + invalid.Message));
            return findings.ToImmutable();
        }

        var events = ((DagLedgerFilesLoadOutcome.Loaded)loadOutcome).Events;
        var frozenPaths = events
            .Where(static item => item.EventType is "Freeze" or "Reattest" or "EnvironmentRecoordinate")
            .Select(static item => item.Input?.DescriptorSelector)
            .Where(static path => path is not null)
            .Select(static path => path!)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var addedEventPaths = context.Changes.Entries
            .Where(static change => change.Kind == RawChangeKind.Added
                && FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        if (context.Changes.Paths.Any(static path => IsFrozenEnvironmentPin(path.Value)))
        {
            try
            {
                findings.AddRange(FrozenStatementIdentityDrift(context, events, addedEventPaths));
            }
            catch (FormatException exception)
            {
                findings.Add(new RuleFinding(
                    FrozenLedgerChangeClassifier.AcceptedRoot,
                    "candidate frozen ledger is invalid: " + exception.Message));
            }
        }

        var reattestedPaths = events
            .Where(item => item.EventType == "Reattest"
                && addedEventPaths.Contains(item.SourcePath))
            .Select(static item => item.Input?.DescriptorSelector)
            .Where(static path => path is not null)
            .Select(static path => path!)
            .ToImmutableHashSet(StringComparer.Ordinal);

        foreach (var change in context.Changes.Entries)
        {
            var path = change.Path.Value;
            if (!path.EndsWith(".lean", StringComparison.Ordinal) || !frozenPaths.Contains(path))
            {
                continue;
            }

            if (change.Kind == RawChangeKind.Deleted)
            {
                findings.Add(new RuleFinding(
                    path,
                    "already-frozen module was deleted; deletion is not supported (revocation "
                    + "flow remains open) and the frozen fragment must not be changed"));
            }
            else if (change.Kind == RawChangeKind.Modified && !reattestedPaths.Contains(path))
            {
                findings.Add(new RuleFinding(
                    path,
                    $"already-frozen module must not be modified without a matching added "
                    + $"Reattest event; run ledger-reattest for {path}"));
            }
        }

        return findings.ToImmutable();
    }

    private static bool IsFrozenEnvironmentPin(string path) =>
        path is "lean-toolchain" or "lakefile.toml" or "lakefile.lean" or "lake-manifest.json";

    private static ImmutableArray<RuleFinding> FrozenStatementIdentityDrift(
        RuleEvaluationContext context,
        ImmutableArray<DagLedgerFileEvent> events,
        ImmutableHashSet<RepoPath> addedEventPaths)
    {
        var addedRecoordinates = events
            .Where(item => item.EventType == "EnvironmentRecoordinate"
                && addedEventPaths.Contains(item.SourcePath))
            .Select(static item => FrozenLedger.ParseEnvironmentRecoordinate(item.Payload))
            .ToImmutableArray();
        var supersededAttestations = events
            .Where(item => item.EventType == "Reattest"
                || item.EventType == "EnvironmentRecoordinate"
                    && !addedEventPaths.Contains(item.SourcePath))
            .Select(static item => RequiredLedgerString(item.Payload, "previous_attestation_event_hash"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var revokedNodeIds = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => RequiredLedgerStringArray(item.Payload, "affected_frozen_node_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var activeByPath = new Dictionary<string, ActiveFrozenStatementIdentity>(
            StringComparer.Ordinal);
        foreach (var attestation in events
            .Where(item => item.EventType is "Freeze" or "Reattest"
                || item.EventType == "EnvironmentRecoordinate"
                    && !addedEventPaths.Contains(item.SourcePath))
            .Where(item => !supersededAttestations.Contains(item.EventHash)
                && !revokedNodeIds.Contains(item.Identity)))
        {
            var path = attestation.Input?.DescriptorSelector
                ?? throw new FormatException("active frozen attestation is missing descriptor_selector.");
            var declarations = attestation.EventType == "EnvironmentRecoordinate"
                ? FrozenLedger.ParseEnvironmentRecoordinate(attestation.Payload).NewDeclarationStatementIds
                : FrozenLedger.ParseDeclarationStatementIds(attestation.Payload);
            if (!activeByPath.TryAdd(path, new ActiveFrozenStatementIdentity(
                declarations,
                attestation.EventHash,
                attestation.Identity)))
            {
                throw new FormatException($"multiple active frozen attestations target {path}.");
            }
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (pathText, active) in activeByPath.OrderBy(
            static item => item.Key,
            StringComparer.Ordinal))
        {
            if (!RepoPath.TryCreate(pathText, out var path))
            {
                throw new FormatException($"active frozen attestation has invalid descriptor_selector {pathText}.");
            }

            var actual = context.Lean.Report.Files.TryGetValue(path, out var report)
                ? CanonicalStatementWriter.DeclarationStatementIds(path, report)
                : ImmutableArray<FrozenDeclarationStatement>.Empty;
            var driftCount = DeclarationStatementDriftCount(active.Declarations, actual);
            if (driftCount > 0 && !addedRecoordinates.Any(payload =>
                RecoordinatesActiveIdentity(payload, active, path, actual)))
            {
                findings.Add(new RuleFinding(
                    pathText,
                    $"frozen module {pathText} has {driftCount} declaration statement identity "
                    + $"drift{(driftCount == 1 ? string.Empty : "s")} after Lean environment pin change"));
            }
        }

        return findings.ToImmutable();
    }

    private static bool RecoordinatesActiveIdentity(
        FrozenEnvironmentRecoordinatePayload payload,
        ActiveFrozenStatementIdentity active,
        RepoPath path,
        ImmutableArray<FrozenDeclarationStatement> actual)
    {
        if (payload.NewInput.DescriptorSelector != path.Value
            || payload.PreviousAttestationEventHash != active.EventHash
            || payload.OldFrozenNodeId.Value != active.FrozenNodeIdentity
            || !payload.OldDeclarationStatementIds.SequenceEqual(active.Declarations)
            || !payload.NewDeclarationStatementIds.SequenceEqual(actual))
        {
            return false;
        }

        var actualStatementId = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(path, actual).AsSpan()));
        return payload.NewStatementId == actualStatementId;
    }

    private static int DeclarationStatementDriftCount(
        ImmutableArray<FrozenDeclarationStatement> expected,
        ImmutableArray<FrozenDeclarationStatement> actual)
    {
        var expectedByName = expected.ToDictionary(
            static item => item.DeclarationNameKey,
            StringComparer.Ordinal);
        var actualByName = actual.ToDictionary(
            static item => item.DeclarationNameKey,
            StringComparer.Ordinal);
        return expectedByName.Keys
            .Union(actualByName.Keys, StringComparer.Ordinal)
            .Count(name => !expectedByName.TryGetValue(name, out var expectedDeclaration)
                || !actualByName.TryGetValue(name, out var actualDeclaration)
                || expectedDeclaration != actualDeclaration);
    }

    private sealed record ActiveFrozenStatementIdentity(
        ImmutableArray<FrozenDeclarationStatement> Declarations,
        string EventHash,
        string FrozenNodeIdentity);

    private static string RequiredLedgerString(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var child) || child.ValueKind != JsonValueKind.String)
        {
            throw new FormatException($"frozen ledger field {property} must be a string.");
        }

        return child.GetString()
            ?? throw new FormatException($"frozen ledger field {property} must not be null.");
    }

    private static ImmutableArray<string> RequiredLedgerStringArray(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var child) || child.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"frozen ledger field {property} must be an array.");
        }

        return child.EnumerateArray()
            .Select(item => item.ValueKind == JsonValueKind.String
                ? item.GetString()
                    ?? throw new FormatException($"frozen ledger field {property} contains null.")
                : throw new FormatException($"frozen ledger field {property} must contain strings."))
            .ToImmutableArray();
    }

    private static ImmutableArray<RuleFinding> Generality(RuleEvaluationContext context)
    {
        var headers = FormalFiles(context.Current)
            .Select(item => (item.Path, Header: TryHeader(item.File.Text, out var header) ? header : null))
            .Where(static item => item.Header is not null)
            .ToDictionary(static item => item.Path.Value, static item => item.Header, StringComparer.Ordinal);
        var imports = context.Lean.Report.Files.ToDictionary(
            static item => item.Key.Value,
            static item => item.Value.Imports
                .Where(static module => module.StartsWith("D5.", StringComparison.Ordinal))
                .Select(static module => module.Replace('.', '/') + ".lean")
                .ToImmutableArray(),
            StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (source, header) in headers)
        {
            if (header?.Generality != "G")
            {
                continue;
            }

            foreach (var target in ImportClosure(source, imports))
            {
                if (headers.TryGetValue(target, out var imported)
                    && imported?.Generality is "I" or "E")
                {
                    findings.Add(new RuleFinding(
                        source,
                        $"G artifact imports {imported.Generality} fact {target}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Domains(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var path in context.Current.Files.Keys)
        {
            var parts = path.Value.Split('/');
            int stratumIndex;
            string label;
            if (parts.Length >= 4 && parts[0] == "D5")
            {
                stratumIndex = 1;
                label = "domain";
            }
            else if (parts.Length >= 5
                && (parts[0] is "Blueprint" or "Evidence")
                && parts[1] == "D5")
            {
                stratumIndex = 2;
                label = parts[0] == "Blueprint" ? "mirror domain" : "domain";
            }
            else
            {
                continue;
            }

            if (!IsStratum(parts[stratumIndex]))
            {
                continue;
            }

            var stratum = parts[stratumIndex];
            var domain = parts[stratumIndex + 1];
            var policyDomain = context.Policy.Domains.FirstOrDefault(
                item => string.Equals(item.Key.Value, domain, StringComparison.Ordinal));
            if (policyDomain.Key is null)
            {
                findings.Add(new RuleFinding(path.Value, $"{label} '{domain}' is not controlled"));
            }
            else if (!string.Equals(policyDomain.Value.ToString(), stratum, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"domain {domain} belongs to {policyDomain.Value}, not {stratum}"));
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> Headers(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var headers = new List<(RepoPath Path, HeaderData Header)>();
        var counts = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, file) in FormalFiles(context.Current))
        {
            if (!TryHeader(file.Text, out var header))
            {
                findings.Add(new RuleFinding(path.Value, "expected the exact six-line header at byte zero"));
                continue;
            }

            headers.Add((path, header));
            counts[header.Gid] = counts.GetValueOrDefault(header.Gid) + 1;
        }

        foreach (var (path, header) in headers)
        {
            var expected = path.Value[..^5];
            if (counts[header.Gid] == 1
                && Gid.TryParse(header.Gid, out _)
                && !string.Equals(header.Gid, expected, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(path.Value, $"GID '{header.Gid}' does not match '{expected}'"));
            }
        }

        return findings.ToImmutable();
    }

}
