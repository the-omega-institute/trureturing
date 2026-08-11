using System.Collections.Immutable;
using System.Diagnostics;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

internal sealed record FileMapFinding(string Code, string Path, string Message);

internal static class FileMapPolicy
{
    private const string RunLocalTrackedMessage =
        "run-local artifact must be removed from the Git index; "
        + "the FILEMAP declaration must not be changed to make this finding go away";
    private const string BackfillLoaderPath =
        "Meta/StrataLint/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs";
    private const string FileMapLoaderPath =
        "Meta/StrataLint/StrataLint.Scribe/FileMap/FileMapManifest.cs";
    private const string LibraryNoteCatalogPath =
        "Meta/StrataLint/StrataLint.Scribe/Library/LibraryNoteCatalog.cs";
    private const string PapergenCommandPath =
        "Meta/StrataLint/StrataLint.Cli/Commands/Papergen/PapergenCommand.cs";
    private const string RegistryLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Commands/RegistryLoader.cs";
    private const string ScribeProjectPath =
        "Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string SnapshotDecoderPath =
        "Meta/StrataLint/StrataLint.Engine/Snapshot/RepositorySnapshot.cs";
    private const string StatementProjectionFixtureLoaderPath =
        "Meta/StrataLint/StrataLint.Scribe/Projection/StatementProjection.cs";
    private const string TomlGoldenLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/TomlGoldenLoader.cs";
    private const string TheoryAtomizerDataLoaderPath =
        "Meta/StrataLint/StrataLint.Engine/Digestion/Configuration/TheoryAtomizerDataLoader.cs";
    private const string GoldenFixtureRegistryLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/GoldenFixtureRegistryLoader.cs";
    private const string GateAuthorityRootCatalogLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/GateAuthority/GateAuthorityRootCatalogLoader.cs";
    private const string PerfBudgetLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Performance/PerfBudgetLoader.cs";
    private const string ValuesKernelLoaderPath =
        "Meta/StrataLint/StrataLint.Scribe/Values/ValuesKernelDataLoader.cs";
    private const string YamlSubsetParserPath =
        "Meta/StrataLint/StrataLint.Engine/Coordinates/YamlSubsetParser.cs";
    private const string C0CertificatePath =
        "Meta/StrataLint/Golden/c0-inaugural-conservative-certificate.json";

    private static readonly Regex LeanImportPattern = new(
        "(?m)^\\s*import\\s+(?<module>[A-Za-z0-9_.]+)\\s*$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    private static readonly IReadOnlyDictionary<string, string> DataVerifierImplementations =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["BackfillInventoryLoader"] = BackfillLoaderPath,
            ["FileMapLoader"] = FileMapLoaderPath,
            ["GoldenFixtureRegistryLoader"] = GoldenFixtureRegistryLoaderPath,
            ["GateAuthorityRootCatalogLoader"] = GateAuthorityRootCatalogLoaderPath,
            ["LibraryNoteCatalog"] = LibraryNoteCatalogPath,
            ["PapergenCommand"] = PapergenCommandPath,
            ["PerfBudgetLoader"] = PerfBudgetLoaderPath,
            ["RegistryLoader"] = RegistryLoaderPath,
            ["ScribeCompiler"] = ScribeProjectPath,
            ["SnapshotDecoder"] = SnapshotDecoderPath,
            ["StatementProjectionFixtureLoader"] = StatementProjectionFixtureLoaderPath,
            ["TomlGoldenLoader"] = TomlGoldenLoaderPath,
            ["TheoryAtomizerDataLoader"] = TheoryAtomizerDataLoaderPath,
            ["ValuesKernelDataLoader"] = ValuesKernelLoaderPath,
            ["YamlSubsetParser"] = YamlSubsetParserPath,
        };

    // FILEMAP names the producer, consumers and verifiers of every generated artifact,
    // but those names were free text that nothing checked, so they went stale the moment
    // the named type was deleted: #1112 removed ValuesProjectionLoader and its FILEMAP
    // consumer entry kept naming it. A declaration nobody verifies is a claim
    // about the system that can quietly stop being true. This resolves each name as a
    // rule rather than a hand-kept table: it must be a declared type in the tracked C#
    // sources, or one of the few deliberate non-type words.
    private static readonly ImmutableHashSet<string> GeneratedActorWords =
        ["reader", "harness-gate", "none"];

    // kind=data 的 verified_by 曾只被「至少有一个真 verifier」检查(InspectDataVerifiers),
    // 所以一个名字死掉后,只要同条目还留着另一个活的,就永远查不出来:#1116 删掉 emit-check
    // 目标之后,`Library/*/*.md` 仍写着它,而 LibraryNoteCatalog 还在,于是 `.Any(...)` 放行。
    // 这里补上逐名检查——每个名字要么是已知的 loader/schema 实现,要么是规则号那种刻意的
    // 非类型名。规则号形如 SL-017,由 RuleId 的封闭字母表背书,不是自由文本。
    private static readonly Regex DataVerifierRuleName = new(
        @"^SL-\d{3}$",
        RegexOptions.CultureInvariant);

    private static readonly Regex TypeDeclarationPattern = new(
        @"\b(?:class|record|interface|struct)\s+([A-Za-z_][A-Za-z0-9_]*)",
        RegexOptions.CultureInvariant);

    private static ImmutableHashSet<string> DeclaredTypeNames(
        string repositoryRoot,
        IEnumerable<string> trackedPaths) =>
        trackedPaths
            .Where(static path => path.EndsWith(".cs", StringComparison.Ordinal))
            .SelectMany(path => TypeDeclarationPattern
                .Matches(File.ReadAllText(Absolute(repositoryRoot, path)))
                .Select(static match => match.Groups[1].Value))
            .ToImmutableHashSet(StringComparer.Ordinal);

    internal static IReadOnlyList<FileMapFinding> InspectDeclaredActors(
        FileMapManifest manifest,
        IReadOnlySet<string> declaredTypes)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(declaredTypes);
        var findings = new List<FileMapFinding>();
        foreach (var entry in manifest.Entries.Where(
            static item => item.Kind is FileMapKind.Generated))
        {
            var declared = new List<(string Field, string Name)> { ("produced_by", entry.ProducedBy) };
            declared.AddRange(entry.ConsumedBy.Select(static name => ("consumed_by", name)));
            declared.AddRange(entry.VerifiedBy.Select(static name => ("verified_by", name)));
            foreach (var (field, name) in declared.Where(item =>
                !GeneratedActorWords.Contains(item.Name)
                && !declaredTypes.Contains(item.Name)))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-ACTOR-DANGLING",
                    entry.Pattern,
                    $"{field} names {name}, which is neither a declared type nor a deliberate word"));
            }
        }

        return findings;
    }

    internal static IReadOnlyList<FileMapFinding> InspectRepository(string repositoryRoot)
    {
        var manifest = FileMapLoader.LoadRepository(repositoryRoot);
        var paths = TrackedPaths(repositoryRoot);
        var trackedModes = TrackedModes(repositoryRoot);
        var files = paths
            .Where(path => path.EndsWith(".lean", StringComparison.Ordinal)
                || IsMachineDataCandidate(path, manifest))
            .ToDictionary(
                static path => path,
                path => File.ReadAllText(Absolute(repositoryRoot, path)),
                StringComparer.Ordinal);
        var availableVerifiers = DataVerifierImplementations
            .Where(pair => File.Exists(Absolute(repositoryRoot, pair.Value))
                && manifest.Match(pair.Value) is [{ Kind: FileMapKind.Program }])
            .Select(static pair => pair.Key)
            .ToHashSet(StringComparer.Ordinal);
        var registry = RegistryLoader.Load(
            File.ReadAllBytes(Absolute(repositoryRoot, "Meta/registry.yaml")),
            File.ReadAllBytes(Absolute(repositoryRoot, "Meta/domains.yaml")));
        var registryFindings = registry is RegistryLoadOutcome.Accepted accepted
            ? InspectRegistryRootAlignment(
                accepted.Policy.RootFiles.Select(static path => path.Value),
                paths.Where(static path => !path.Contains('/', StringComparison.Ordinal)))
            : [new FileMapFinding(
                "FILEMAP-REGISTRY-ALIGNMENT",
                "Meta/registry.yaml",
                "registry failed to load before FILEMAP alignment")];

        return InspectCoverage(manifest, paths)
            .Concat(registryFindings)
            .Concat(InspectDeclaredActors(manifest, DeclaredTypeNames(repositoryRoot, paths)))
            .Concat(InspectDataVerifiers(manifest, availableVerifiers))
            .Concat(InspectDataVerifierNames(manifest, availableVerifiers))
            .Concat(InspectGeneratedInventory(manifest, paths, GeneratedArtifactInventory.All))
            .Concat(InspectDeclaredModes(manifest, trackedModes))
            .Concat(InspectDirectoryKinds(manifest, paths))
            .Concat(InspectDependencies(manifest, files))
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
            .ToArray();
    }

    internal static IReadOnlyList<FileMapFinding> InspectDeclaredModes(
        FileMapManifest manifest,
        IReadOnlyDictionary<string, string> trackedModes)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(trackedModes);
        return manifest.Entries
            .Where(static entry => entry.Kind is FileMapKind.Generated
                && entry.ArtifactId != "none"
                && entry.RuntimeDisposition == "committed-source")
            .Where(entry => !trackedModes.TryGetValue(entry.Pattern, out var actual)
                || !string.Equals(entry.Mode, actual, StringComparison.Ordinal))
            .Select(entry => new FileMapFinding(
                "FILEMAP-GENERATED-MODE",
                entry.Pattern,
                trackedModes.TryGetValue(entry.Pattern, out var actual)
                    ? $"declared Git mode {entry.Mode} differs from index mode {actual}"
                    : "declared committed artifact is absent from the Git index"))
            .ToArray();
    }

    internal static IReadOnlyList<FileMapFinding> InspectGeneratedInventory(
        FileMapManifest manifest,
        IEnumerable<string> trackedPaths,
        IReadOnlyList<GeneratedArtifactIdentity> inventory)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(trackedPaths);
        ArgumentNullException.ThrowIfNull(inventory);
        var tracked = trackedPaths.ToHashSet(StringComparer.Ordinal);
        var findings = new List<FileMapFinding>();
        var inventoryPaths = inventory.Select(static artifact => artifact.Path)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var artifact in inventory.OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            var artifactFindings = new List<FileMapFinding>();
            var matches = manifest.Match(artifact.Path);
            if (matches is not [var generated])
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-JOIN",
                    artifact.Path,
                    $"canonical producer inventory requires exactly one FILEMAP match, found {matches.Length}"));
                findings.AddRange(artifactFindings);
                continue;
            }

            if (generated.RuntimeDisposition == "run-local"
                && !string.Equals(generated.Pattern, artifact.Path, StringComparison.Ordinal))
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-LITERAL",
                    artifact.Path,
                    $"canonical producer inventory requires a literal FILEMAP pattern, found {generated.Pattern}"));
            }

            if (generated.Kind is not FileMapKind.Generated)
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-KIND",
                    artifact.Path,
                    $"canonical producer inventory requires generated kind, found {generated.Kind}"));
            }

            var isTracked = tracked.Contains(artifact.Path);
            if (generated.RuntimeDisposition == "run-local" && isTracked)
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-RUN-LOCAL-TRACKED",
                    artifact.Path,
                    RunLocalTrackedMessage));
            }

            if (generated.RuntimeDisposition == "run-local"
                && (generated.ArtifactId == "none" || generated.Mode != "100644"
                    || generated.HistoryRequirement != "not-required"))
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-RUN-LOCAL",
                    artifact.Path,
                    "run-local join requires artifact_id, mode 100644, and history_requirement not-required"));
            }

            if (!string.Equals(generated.ArtifactId, artifact.ArtifactId, StringComparison.Ordinal))
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-ARTIFACT-ID",
                    artifact.Path,
                    $"FILEMAP artifact_id {generated.ArtifactId} differs from inventory artifact_id {artifact.ArtifactId}"));
            }

            if (!string.Equals(generated.ProducedBy, artifact.Producer, StringComparison.Ordinal))
            {
                artifactFindings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-PRODUCER",
                    artifact.Path,
                    $"FILEMAP producer {generated.ProducedBy} differs from inventory producer {artifact.Producer}"));
            }

            findings.AddRange(artifactFindings);
            if (isTracked || (artifactFindings.Count == 0 && generated.RuntimeDisposition == "run-local"))
            {
                continue;
            }

            findings.Add(new FileMapFinding(
                "FILEMAP-GENERATED-STALE-INVENTORY",
                artifact.Path,
                "producer inventory output is absent from tracked repository files"));
        }

        foreach (var path in tracked.Order(StringComparer.Ordinal))
        {
            if (manifest.Match(path) is not [var generated]
                || generated.Kind is not FileMapKind.Generated)
            {
                continue;
            }

            if (generated.RuntimeDisposition == "run-local"
                && IsDataKeyedGeneratedSet(generated))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-RUN-LOCAL-TRACKED",
                    path,
                    RunLocalTrackedMessage));
                continue;
            }

            if (
                // The canonical inventory enumerates products whose paths are known at compile time.
                // A glob set without an aggregate identity derives its member keys from governed data,
                // so its members cannot be enumerated by the program. FILEMAP already declares producer
                // ownership, and RepositoryPathPolicy enforces the directory-closure path predicate;
                // repeating the per-member inventory join would add no information.
                !IsDataKeyedGeneratedSet(generated)
                && !inventoryPaths.Contains(path))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-INVENTORY",
                    path,
                    "generated file is absent from the canonical producer inventory"));
            }
        }

        return findings;
    }

    private static bool IsDataKeyedGeneratedSet(FileMapEntry entry) =>
        string.Equals(entry.ArtifactId, "none", StringComparison.Ordinal)
        && (entry.Pattern.Contains('*') || entry.Pattern.Contains('?'));

    internal static IReadOnlyList<FileMapFinding> InspectRegistryRootAlignment(
        IEnumerable<string> registryRootFiles,
        IEnumerable<string> trackedRootFiles)
    {
        ArgumentNullException.ThrowIfNull(registryRootFiles);
        ArgumentNullException.ThrowIfNull(trackedRootFiles);
        var registry = registryRootFiles.ToHashSet(StringComparer.Ordinal);
        var tracked = trackedRootFiles.ToHashSet(StringComparer.Ordinal);
        if (registry.SetEquals(tracked))
        {
            return [];
        }

        var registryOnly = registry.Except(tracked, StringComparer.Ordinal).Order(StringComparer.Ordinal);
        var trackedOnly = tracked.Except(registry, StringComparer.Ordinal).Order(StringComparer.Ordinal);
        return
        [
            new FileMapFinding(
                "FILEMAP-REGISTRY-ALIGNMENT",
                "Meta/registry.yaml",
                $"registry-only [{string.Join(", ", registryOnly)}]; "
                + $"tracked-only [{string.Join(", ", trackedOnly)}]"),
        ];
    }

    internal static IReadOnlyList<FileMapFinding> InspectCoverage(
        FileMapManifest manifest,
        IEnumerable<string> paths)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(paths);
        var findings = new List<FileMapFinding>();
        foreach (var path in paths.Order(StringComparer.Ordinal))
        {
            var matches = manifest.Match(path);
            if (matches.Length == 0)
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-UNCLASSIFIED",
                    path,
                    "tracked repository file matches no FILEMAP pattern"));
            }
            else if (matches.Length > 1)
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-AMBIGUOUS",
                    path,
                    "tracked repository file matches multiple FILEMAP patterns: "
                    + string.Join(", ", matches.Select(static entry => entry.Pattern))));
            }
        }

        return findings;
    }

    internal static IReadOnlyList<FileMapFinding> InspectDataVerifiers(
        FileMapManifest manifest,
        IReadOnlySet<string> availableVerifierNames)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(availableVerifierNames);
        return manifest.Entries
            .Where(static entry => entry.Kind is FileMapKind.Data)
            .Where(entry => !entry.VerifiedBy.Any(availableVerifierNames.Contains))
            .Select(static entry => new FileMapFinding(
                "FILEMAP-DATA-VERIFIER",
                entry.Pattern,
                "data pattern names no existing loader/schema verifier"))
            .ToArray();
    }

    internal static IReadOnlyList<FileMapFinding> InspectDataVerifierNames(
        FileMapManifest manifest,
        IReadOnlySet<string> availableVerifierNames)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(availableVerifierNames);
        return manifest.Entries
            .Where(static entry => entry.Kind is FileMapKind.Data)
            .SelectMany(entry => entry.VerifiedBy
                .Where(name => !availableVerifierNames.Contains(name)
                    && !DataVerifierRuleName.IsMatch(name))
                .Select(name => new FileMapFinding(
                    "FILEMAP-DATA-VERIFIER-DANGLING",
                    entry.Pattern,
                    $"verified_by names {name}, which is neither a known "
                    + "loader/schema verifier nor a rule id")))
            .ToArray();
    }

    internal static IReadOnlyList<FileMapFinding> InspectDirectoryKinds(
        FileMapManifest manifest,
        IEnumerable<string> paths)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(paths);
        var trackedPaths = paths.Order(StringComparer.Ordinal).ToArray();
        var findings = new List<FileMapFinding>();
        foreach (var path in trackedPaths)
        {
            var matches = manifest.Match(path);
            if (matches.Length != 1)
            {
                continue;
            }

            var entry = matches[0];
            var kind = entry.Kind;
            if (path.Split('/').Contains("Generated", StringComparer.Ordinal)
                && kind is not FileMapKind.Generated
                || path.StartsWith("Golden/cases/", StringComparison.Ordinal)
                    && kind is not FileMapKind.Data
                || path.StartsWith("Golden/Projection/", StringComparison.Ordinal)
                    && kind is not FileMapKind.Data
                || (path.StartsWith("Meta/StrataLint/Golden/Frozen/", StringComparison.Ordinal)
                        || path == C0CertificatePath)
                    && kind is not FileMapKind.Ledger)
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-DIRECTORY-KIND",
                    path,
                    $"class directory contains {KindName(kind)} content"));
            }

            if (path.StartsWith("Meta/StrataLint/", StringComparison.Ordinal)
                && kind is FileMapKind.Data
                && !entry.ResidenceViolation)
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-DATA-RESIDENCE",
                    path,
                    "data must live outside the Meta/StrataLint protected program surface"));
            }

            if (entry.ResidenceViolation
                && !path.StartsWith("Meta/StrataLint/", StringComparison.Ordinal))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-RESIDENCE-MARKER",
                    path,
                    "residence_violation may mark only data in the protected program surface"));
            }
        }

        var violations = ResidenceViolations(manifest, trackedPaths);
        if (violations.Count != manifest.ResidencePolicy.KnownViolationCount)
        {
            findings.Add(new FileMapFinding(
                "FILEMAP-RESIDENCE-DRIFT",
                FileMapLoader.RelativePath,
                $"policy freezes {manifest.ResidencePolicy.KnownViolationCount} violations but repository has {violations.Count}"));
        }

        return findings;
    }

    internal static IReadOnlyList<string> ResidenceViolations(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        return ResidenceViolations(
            FileMapLoader.LoadRepository(repositoryRoot),
            TrackedPaths(repositoryRoot));
    }

    internal static IReadOnlyList<string> ResidenceViolations(
        FileMapManifest manifest,
        IEnumerable<string> paths)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(paths);
        return paths
            .Where(path => path.StartsWith("Meta/StrataLint/", StringComparison.Ordinal))
            .Where(path => manifest.Match(path) is
                [{ Kind: FileMapKind.Data, ResidenceViolation: true }])
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    internal static IReadOnlyList<FileMapFinding> InspectDependencies(
        FileMapManifest manifest,
        IReadOnlyDictionary<string, string> files)
    {
        ArgumentNullException.ThrowIfNull(manifest);
        ArgumentNullException.ThrowIfNull(files);
        var findings = new List<FileMapFinding>();
        var generatedPaths = files.Keys
            .Where(path => manifest.Match(path) is [{ Kind: FileMapKind.Generated }])
            .Order(StringComparer.Ordinal)
            .ToArray();
        foreach (var (path, source) in files.OrderBy(static pair => pair.Key, StringComparer.Ordinal))
        {
            var matches = manifest.Match(path);
            if (matches.Length != 1)
            {
                continue;
            }

            if (matches[0].Kind is FileMapKind.Data
                && path != FileMapLoader.RelativePath
                && IsMachineDataPath(path))
            {
                foreach (var generatedPath in generatedPaths.Where(source.Contains))
                {
                    findings.Add(new FileMapFinding(
                        "FILEMAP-DATA-GENERATED-DEPENDENCY",
                        path,
                        $"machine-readable data references generated artifact {generatedPath}"));
                }
            }

            if (!path.EndsWith(".lean", StringComparison.Ordinal))
            {
                continue;
            }

            foreach (Match import in LeanImportPattern.Matches(source))
            {
                var importedPath = import.Groups["module"].Value.Replace('.', '/') + ".lean";
                if (manifest.Match(importedPath) is [{ Kind: FileMapKind.Generated }])
                {
                    findings.Add(new FileMapFinding(
                        "FILEMAP-LEAN-GENERATED-IMPORT",
                        path,
                        $"Lean imports generated artifact {importedPath}"));
                }
            }
        }

        return findings;
    }

    private static bool IsMachineDataCandidate(string path, FileMapManifest manifest) =>
        manifest.Match(path) is [{ Kind: FileMapKind.Data }] && IsMachineDataPath(path);

    private static bool IsMachineDataPath(string path) =>
        path.EndsWith(".toml", StringComparison.Ordinal)
        || path.EndsWith(".yaml", StringComparison.Ordinal)
        || path.EndsWith(".yml", StringComparison.Ordinal)
        || path.EndsWith(".json", StringComparison.Ordinal)
        || path.EndsWith(".scribe.cs", StringComparison.Ordinal);

    private static string[] TrackedPaths(string repositoryRoot)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        startInfo.ArgumentList.Add("-C");
        startInfo.ArgumentList.Add(repositoryRoot);
        startInfo.ArgumentList.Add("ls-files");
        startInfo.ArgumentList.Add("--cached");
        startInfo.ArgumentList.Add("--others");
        startInfo.ArgumentList.Add("--exclude-standard");
        startInfo.ArgumentList.Add("-z");
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git ls-files for FILEMAP");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"git ls-files failed with exit {process.ExitCode}: {error}");
        }

        return output.Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static IReadOnlyDictionary<string, string> TrackedModes(string repositoryRoot)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        startInfo.ArgumentList.Add("-C");
        startInfo.ArgumentList.Add(repositoryRoot);
        startInfo.ArgumentList.Add("ls-files");
        startInfo.ArgumentList.Add("--stage");
        startInfo.ArgumentList.Add("-z");
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git ls-files --stage for FILEMAP");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"git ls-files --stage failed with exit {process.ExitCode}: {error}");
        }

        return output.Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Select(static line => line.Split([' ', '\t'], 4, StringSplitOptions.RemoveEmptyEntries))
            .Where(static fields => fields.Length == 4 && fields[2] == "0")
            .ToDictionary(static fields => fields[3], static fields => fields[0], StringComparer.Ordinal);
    }

    private static string KindName(FileMapKind kind) => kind.ToString().ToLowerInvariant();

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
}
