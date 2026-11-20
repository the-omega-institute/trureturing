using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ScopedAdmissionReports
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static RawChangeSet ChangedPaths(string manifest, PreparedRepository? prepared)
    {
        var changed = RawChangeSet.Create(ReadManifest(manifest));
        if (prepared is not null)
        {
            // A copy source appears in --find-copies-harder output as provenance
            // even though its bytes did not change in the candidate.
            var expected = prepared.Changes.Entries.Where(change => change.Kind != RawChangeKind.Copied)
                .Select(change => change.Path).ToHashSet();
            if (!expected.SetEquals(changed.Paths))
                throw new InvalidDataException("changed-path manifest differs from the protected-base delta");
        }
        return changed;
    }

    internal static LeanAxiomReport Read(string repositoryRoot, RepositorySnapshot snapshot,
        ImmutableArray<string> expectedTargets, string? manifest)
    {
        var paths = manifest is null ? [] : ReadManifest(manifest)
            .Select(path => Path.GetFullPath(path, repositoryRoot)).ToArray();
        if (paths.Length != paths.Distinct(StringComparer.Ordinal).Count())
            throw new InvalidDataException("duplicate artifact in scoped report manifest");

        var expected = expectedTargets.ToImmutableHashSet(StringComparer.Ordinal);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var files = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        var digests = new Dictionary<RepoPath, string>();
        foreach (var path in paths)
        {
            using var bundle = new PrecomputedLeanReportSource.CapturedBundle(repositoryRoot, path);
            using var provenance = bundle.CaptureProvenance();
            var inputRoots = provenance.RootElement.GetProperty("inputs").GetProperty("scope").GetProperty("roots");
            var roots = inputRoots.EnumerateArray().Select(root => root.GetString()
                ?? throw new InvalidDataException("null root in scoped Lean report")).ToArray();
            if (roots.Length == 0 || roots.Any(root => !expected.Contains(root)))
                throw new InvalidDataException($"unexpected roots in scoped Lean report {path}");

            var scope = LeanReportScope.Create(snapshot, roots.Select(root => RepoPath.CreateKnown(root.Replace('.', '/') + ".lean")));
            var report = bundle.Load(scope);
            // Check configuration, dependency sources and production provenance against this checkout.
            bundle.ValidateForEmission();
            seen.UnionWith(roots);

            // The bundle verifier authenticates each per-module digest against its complete
            // report row. Two document batches may share roots and import dependencies.
            var origins = provenance.RootElement.GetProperty("module_origins");
            foreach (var (source, row) in report.Files)
            {
                var digest = origins.GetProperty(LeanImportClosure.ModuleName(source)).GetProperty("report_sha256").GetString()
                    ?? throw new InvalidDataException("missing scoped report module digest");
                if (digests.TryAdd(source, digest))
                    files.Add(source.Value, row);
                else if (!string.Equals(digests[source], digest, StringComparison.Ordinal))
                    throw new InvalidDataException("scoped reports disagree on " + source.Value);
            }
        }
        if (!seen.SetEquals(expected))
            throw new InvalidDataException("scoped Lean report is missing roots: " + string.Join(", ", expected.Except(seen).Order(StringComparer.Ordinal)));
        return LeanAxiomReport.CreateScoped(files);
    }

    private static string[] ReadManifest(string manifest)
    {
        var text = StrictUtf8.GetString(File.ReadAllBytes(manifest));
        if (text.Length == 0) return [];
        if (text[^1] != '\0')
            throw new InvalidDataException("expected a NUL-terminated path manifest: " + manifest);
        var paths = text[..^1].Split('\0');
        if (paths.Any(string.IsNullOrEmpty))
            throw new InvalidDataException("empty path in manifest: " + manifest);
        return paths;
    }
}
