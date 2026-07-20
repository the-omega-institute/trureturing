using System.Diagnostics;
using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

internal sealed record FileMapFinding(string Code, string Path, string Message);

internal static class FileMapPolicy
{
    private const string BackfillLoaderPath =
        "Meta/StrataLint/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs";
    private const string FileMapLoaderPath =
        "Meta/StrataLint/StrataLint.Scribe/FileMap/FileMapManifest.cs";
    private const string LibraryNoteCatalogPath =
        "Meta/StrataLint/StrataLint.Scribe/Library/LibraryNoteCatalog.cs";
    private const string RegistryLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Commands/RegistryLoader.cs";
    private const string ScribeProjectPath =
        "Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj";
    private const string SnapshotDecoderPath =
        "Meta/StrataLint/StrataLint.Engine/Snapshot/RepositorySnapshot.cs";
    private const string TomlGoldenLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/TomlGoldenLoader.cs";
    private const string GoldenFixtureRegistryLoaderPath =
        "Meta/StrataLint/StrataLint.Cli/Golden/GoldenFixtureRegistryLoader.cs";
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
            ["LibraryNoteCatalog"] = LibraryNoteCatalogPath,
            ["PerfBudgetLoader"] = PerfBudgetLoaderPath,
            ["RegistryLoader"] = RegistryLoaderPath,
            ["ScribeCompiler"] = ScribeProjectPath,
            ["SnapshotDecoder"] = SnapshotDecoderPath,
            ["TomlGoldenLoader"] = TomlGoldenLoaderPath,
            ["ValuesKernelDataLoader"] = ValuesKernelLoaderPath,
            ["YamlSubsetParser"] = YamlSubsetParserPath,
        };

    internal static IReadOnlyList<FileMapFinding> InspectRepository(string repositoryRoot)
    {
        var manifest = FileMapLoader.LoadRepository(repositoryRoot);
        var paths = TrackedPaths(repositoryRoot);
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
            .Concat(InspectDataVerifiers(manifest, availableVerifiers))
            .Concat(InspectGeneratedInventory(manifest, paths, GeneratedArtifactInventory.All))
            .Concat(InspectDirectoryKinds(manifest, paths))
            .Concat(InspectDependencies(manifest, files))
            .OrderBy(static finding => finding.Path, StringComparer.Ordinal)
            .ThenBy(static finding => finding.Code, StringComparer.Ordinal)
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
        var indexed = inventory.ToDictionary(
            static artifact => artifact.Path,
            StringComparer.Ordinal);
        var findings = new List<FileMapFinding>();
        foreach (var path in tracked.Order(StringComparer.Ordinal))
        {
            var matches = manifest.Match(path);
            if (matches is not [{ Kind: FileMapKind.Generated } generated])
            {
                continue;
            }

            if (!indexed.TryGetValue(path, out var artifact))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-INVENTORY",
                    path,
                    "generated file is absent from the canonical producer inventory"));
                continue;
            }

            if (!string.Equals(generated.ProducedBy, artifact.Producer, StringComparison.Ordinal))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-PRODUCER",
                    path,
                    $"FILEMAP producer {generated.ProducedBy} differs from inventory producer {artifact.Producer}"));
            }

            if (artifact.VerifiedBy != "emit-check"
                || !generated.VerifiedBy.Contains("emit-check", StringComparer.Ordinal))
            {
                findings.Add(new FileMapFinding(
                    "FILEMAP-GENERATED-VERIFY",
                    path,
                    "generated file is outside the emit-check coverage set"));
            }
        }

        foreach (var artifact in inventory.Where(artifact => !tracked.Contains(artifact.Path)))
        {
            findings.Add(new FileMapFinding(
                "FILEMAP-GENERATED-STALE-INVENTORY",
                artifact.Path,
                "producer inventory output is absent from tracked repository files"));
        }

        return findings;
    }

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

    private static string KindName(FileMapKind kind) => kind.ToString().ToLowerInvariant();

    private static string Absolute(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
}
