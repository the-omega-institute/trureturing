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
                var findingAffected = IsLeanClosureFactAffected(context, path)
                    || context.IsBaseFactAffected(target);
                if (!context.Current.TryGetFile(target, out _) && findingAffected)
                {
                    findings.Add(new RuleFinding(path.Value, $"managed import {target} does not exist"));
                }
                else if (!ImportAllowed(path.Value, target) && findingAffected)
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
            if (declarations.Length > 0
                && !path.Value.Contains("/X_Frontier/", StringComparison.Ordinal)
                && IsLeanClosureFactAffected(context, path))
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
    // admission rule keeps the unbanded limit, so the next change that introduces a
    // capacity-counted path absent from its ForkPoint is still refused and the split
    // pressure lands exactly where it belongs.
    internal const int DirectoryToleranceLimit = 24;

    // SL-003 capacity exclusions: theory inputs, the Lake manifest, the backfill
    // inventory, atomizer dialect registry, canonical CAS blobs, per-atom
    // formalization receipts, per-test retirement declarations, and generated Blueprint
    // Markdown projections are not artifacts the capacity pressure rule bounds. Machine
    // inventories grow one entry per
    // admitted unit and are never navigated as content buckets; the atomizer registry
    // is one canonical strict-loader input, not a content artifact to split. A
    // Blueprint document's structural slot is its .scribe.cs source. The .md is a FILEMAP
    // generated projection at the same stem, so counting both paths would cap a lawful
    // twelve-module Lean bucket at six blueprinted modules. This exclusion concerns only
    // structural capacity; it gives the projection no content or history authority. Single
    // source shared with the CapacityPolicy dotnet-test net.
    internal static bool IsCapacityExcluded(string path) =>
        path.StartsWith("docs/develop/", StringComparison.Ordinal)
        || string.Equals(path, "lake-manifest.json", StringComparison.Ordinal)
        || string.Equals(path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
        || path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
        || string.Equals(path, TheoryAtomizerDataLoader.DataPath, StringComparison.Ordinal)
        || DigestionCasStore.IsCanonicalPath(path)
        || FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
        || path.StartsWith(DigestionFormalizationReceipt.RootPath, StringComparison.Ordinal)
        || (path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".md", StringComparison.Ordinal));

    // The canonical artifact line count: newline-delimited lines, not counting a
    // trailing terminator. Shared with CapacityPolicy so both nets agree exactly.
    internal static int CountArtifactLines(string text) =>
        text.Split('\n').Length - (text.EndsWith('\n') ? 1 : 0);

    internal static Dictionary<string, HashSet<string>> CapacityPathsByDirectory(
        IEnumerable<RepoPath> paths)
    {
        var directories = new Dictionary<string, HashSet<string>>(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (IsCapacityExcluded(path.Value))
            {
                continue;
            }

            var directory = DirectoryOf(path.Value);
            if (!directories.TryGetValue(directory, out var directoryPaths))
            {
                directoryPaths = new HashSet<string>(StringComparer.Ordinal);
                directories.Add(directory, directoryPaths);
            }

            directoryPaths.Add(path.Value);
        }

        return directories;
    }

    private static ImmutableArray<RuleFinding> Capacity(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        findings.AddRange(ScribeUnknownDebtPolicy.Evaluate(
                ScribeTestMapDeriver.DeriveSnapshot(context.Current),
                ScribeTestMapDeriver.DeriveSnapshot(context.ForkPoint))
            .Select(static finding => new RuleFinding(
                finding.Path,
                finding.Message,
                finding.Effect)));
        foreach (var (path, file) in context.Current.Files)
        {
            if (IsCapacityExcluded(path.Value))
            {
                continue;
            }

            var lineCount = CountArtifactLines(file.Text);
            if (lineCount > ArtifactHardLineLimit)
            {
                // 阻断落在把它推过线的那个候选身上,不落在无辜候选身上。判据取自分叉点:
                // 本次改动有没有让它变长。与目录轴同构(带内候选只有引入了分叉点上不存在的
                // 路径才阻断,见下方 DirectoryToleranceLimit 注释与 2026-08-13 判例)。
                //
                // 案由(2026-08-15):dev 上 DigestionLedgerAligner.cs 因两个 PR 的**并集**
                // 达到 823 行——各自树内是 799 与 639,都没越线,各自 admit 都是对的。此后每个
                // PR 的准入一律判红,包括 #1890/#1891/#1896/#1897 这些从未碰过该文件的,全仓
                // 锁死约一小时。并集本身在 PR 期不可拦(那正是 strict 的活,而 strict 已被 19 禁),
                // 所以能治的是别让它连坐,并把分裂压力压在真正加长它的那次改动上。
                //
                // 检测不降级:超线仍然出 finding,无辜者那条是 Observe;而全仓检测由
                // CapacityPolicy.InspectRepository 在 dotnet test 里承担(它此前无调用者,
                // 同一改动一并接上)。第20条要的正是这个形状:窄化阻断须以加强检测为对价。
                var forkPointLineCount = context.ForkPoint.Files.TryGetValue(path, out var forkFile)
                    ? CountArtifactLines(forkFile.Text)
                    : 0;
                findings.Add(lineCount > forkPointLineCount
                    ? new RuleFinding(path.Value, "artifact exceeds 800 lines")
                    : new RuleFinding(
                        path.Value,
                        $"artifact is overfull at {lineCount} lines (hard limit "
                        + $"{ArtifactHardLineLimit}; split per CLAUDE.md 8), but this change "
                        + "did not grow it",
                        AdmissionEffect.Observe));
            }
            else if (lineCount > ArtifactSoftLineLimit)
            {
                findings.Add(new RuleFinding(
                    path.Value,
                    $"artifact spans {lineCount} lines (soft limit {ArtifactSoftLineLimit}, "
                    + $"hard limit {ArtifactHardLineLimit})",
                    AdmissionEffect.Observe));
            }

        }

        var directories = CapacityPathsByDirectory(context.Current.Files.Keys);
        var forkPointDirectories = CapacityPathsByDirectory(context.ForkPoint.Files.Keys);

        // Occupancy is counted over the whole tree so the number reported is the real one, but
        // only buckets this change touches are reported. DirectoryToleranceLimit above was added
        // so that a union of two independently-admitted PRs would not end up "blocking every
        // unrelated PR until someone splits" - and it was wired into the repository-wide net
        // alone, leaving this rule scanning every directory and blocking them anyway. On
        // 2026-08-13 that is exactly what happened: merge-base aa2deeb held eleven members in
        // D5/S3/Constants, deposits f2296a0 and eb759dc each saw twelve and admitted, and union
        // 0ba924d held thirteen and stopped dev and every unrelated branch. Every member of that
        // bucket is frozen, so moving one out is not an available split. Admission therefore
        // compares capacity-counted path membership with the ForkPoint: a band candidate blocks
        // if any current path is absent there, and otherwise emits a non-blocking Observe.
        //
        // Band closure: for each admitted band candidate C, relative to its own merge base F,
        // Added_C(d) = C(d) \ F(d) is empty because CurrentPaths_C(d) is a subset of
        // MergeBasePaths_C(d). A git three-way merge can introduce only paths in Added_C(d), so
        // every such merge is non-growing in d; the candidates need not share a fork point.
        //
        // Residual: candidates at or below DirectoryFileLimit are not constrained by this
        // predicate. The 2026-08-13 union mechanism in that regime is unchanged by this change;
        // the repository-wide DirectoryToleranceLimit net is its detection layer.
        //
        // Known cost: a same-directory rename arrives as Deleted(old)+Added(new). Honoring that
        // pair as non-growing would break band closure: branch A can rename x to a while branch B
        // renames x to b, making their union contain 25 paths. The gateway asks git to detect
        // renames and copies, but ParseChanges intentionally discards the old/new pairing when it
        // builds RawChangeSet. Retaining that choice is deliberate, so the new path still blocks.
        // Observe remains a structured, non-blocking finding; the current CLI does not render
        // Observe findings on the admit path. That is an existing property of the Observe channel,
        // not a visibility regression introduced here.
        var touched = context.Changes.Paths
            .Select(static path => DirectoryOf(path.Value))
            .ToHashSet(StringComparer.Ordinal);
        findings.AddRange(directories
            .Where(static item => item.Value.Count > DirectoryToleranceLimit)
            .Select(static item => new RuleFinding(
                item.Key,
                $"directory contains {item.Value.Count} files (repository tolerance "
                + $"{DirectoryToleranceLimit}; split per CLAUDE.md 8)")));
        foreach (var item in directories.Where(item => item.Value.Count > DirectoryFileLimit
            && item.Value.Count <= DirectoryToleranceLimit
            && touched.Contains(item.Key)))
        {
            var forkPointPaths = forkPointDirectories.GetValueOrDefault(item.Key);
            if (forkPointPaths is null || !item.Value.IsSubsetOf(forkPointPaths))
            {
                findings.Add(new RuleFinding(
                    item.Key,
                    $"directory contains {item.Value.Count} files (admission limit "
                    + $"{DirectoryFileLimit}, repository tolerance "
                    + $"{DirectoryToleranceLimit}; split per CLAUDE.md 8)"));
            }
            else
            {
                findings.Add(new RuleFinding(
                    item.Key,
                    $"directory is overfull at {item.Value.Count} files (admission limit "
                    + $"{DirectoryFileLimit}, repository tolerance "
                    + $"{DirectoryToleranceLimit}), but this change introduced no capacity-counted "
                    + "path absent from its fork point; split per CLAUDE.md 8",
                    AdmissionEffect.Observe));
            }
        }

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

            if (!MirrorPairAffected(context, path.Value, header))
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
            .Where(item => context.IsBaseFactAffected(item.Key.Value))
            .Where(item => !context.Current.TryGetFile(item.Key.Value, out var current)
                || !current.RawBytes.AsSpan().SequenceEqual(item.Value.RawBytes.AsSpan()))
            .Select(static item => new RuleFinding(item.Key.Value, "tracked Chronicle entries are append-only"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Badges(RuleEvaluationContext context) =>
        context.Current.Files
            .Where(item => IsStatusScope(item.Key.Value)
                && context.IsBaseFactAffected(item.Key.Value)
                && BadgePattern.IsMatch(item.Value.Text))
            .Select(static item => new RuleFinding(item.Key.Value, "hand-written status badge is forbidden"))
            .ToImmutableArray();

    private static ImmutableArray<RuleFinding> Hearts(RuleEvaluationContext context)
    {
        try
        {
            if (context.IsBaseFactAffected(HeartsAuthorizationLedger.Path)
                && context.Current.TryGetFile(
                    HeartsAuthorizationLedger.Path,
                    out var authorizationFile))
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

        }

        return findings.ToImmutable();
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
                    && imported?.Generality is "I" or "E"
                    && IsLeanClosureFactAffected(context, RepoPath.CreateKnown(source)))
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
            if (!context.IsBaseFactAffected(path.Value)
                && !context.IsBaseFactAffected("Meta/domains.yaml")
                && !context.IsBaseFactAffected("Meta/registry.yaml"))
            {
                continue;
            }

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
                if (context.IsBaseFactAffected(path.Value))
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        "expected the exact six-line header at byte zero"));
                }

                continue;
            }

            headers.Add((path, header));
            counts[header.Gid] = counts.GetValueOrDefault(header.Gid) + 1;
        }

        foreach (var (path, header) in headers)
        {
            var expected = path.Value[..^5];
            if (context.IsBaseFactAffected(path.Value)
                && counts[header.Gid] == 1
                && Gid.TryParse(header.Gid, out _)
                && !string.Equals(header.Gid, expected, StringComparison.Ordinal))
            {
                findings.Add(new RuleFinding(path.Value, $"GID '{header.Gid}' does not match '{expected}'"));
            }
        }

        return findings.ToImmutable();
    }

}
