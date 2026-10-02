using System.Collections.Immutable;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Engine;

// Lake declarations determine package membership, including non-default libraries
// whose modules have no Reg prefix. Both snapshots are data; no base code runs.
internal static class RegImplementationBoundary
{
    private const string Lakefile = "Reg/lakefile.toml";
    private readonly record struct Edge(string Path, string Dependency);

    internal static ImmutableArray<RuleFinding> Evaluate(DeltaRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        try
        {
            var baseline = Collect(context.Baseline);
            var candidate = Collect(context.Current);
            foreach (var edge in candidate.Except(baseline).OrderBy(e => e.Path, StringComparer.Ordinal)
                .ThenBy(e => e.Dependency, StringComparer.Ordinal))
                findings.Add(new(edge.Path, $"REG-IMPLEMENTATION: forbidden dependency {edge.Dependency}"));
            foreach (var group in baseline.GroupBy(e => e.Path).OrderBy(g => g.Key, StringComparer.Ordinal))
            {
                var remaining = candidate.Count(e => e.Path == group.Key);
                if (context.Current.TryGetFile(group.Key, out var current)
                    && context.Baseline.TryGetFile(group.Key, out var old)
                    && !current.RawBytes.AsSpan().SequenceEqual(old.RawBytes.AsSpan())
                    && remaining >= group.Count())
                    findings.Add(new(group.Key, "REG-IMPLEMENTATION: changed debt owner must strictly reduce dependencies"));
                findings.Add(new(group.Key,
                    $"REG-IMPLEMENTATION debt: base={group.Count()}, candidate={remaining}", AdmissionEffect.Observe));
            }
        }
        catch (Exception error) when (error is TomlException or FormatException or LeanSourceExtractionException)
        {
            findings.Add(new(Lakefile, $"REG-IMPLEMENTATION: {error.Message}"));
        }
        return findings.ToImmutable();
    }

    private static HashSet<Edge> Collect(RepositorySnapshot snapshot)
    {
        var edges = new HashSet<Edge>();
        // RegManifestAgreement owns the missing-package/configuration diagnostic.
        if (!snapshot.TryGetFile(Lakefile, out var file)) return edges;
        _ = Tomlyn.Parsing.SyntaxParser.ParseStrict(file.Text, sourceName: Lakefile, validate: true);
        var config = TomlSerializer.Deserialize<TomlTable>(file.Text)
            ?? throw new FormatException("Reg Lake configuration is empty");
        var targets = Tables(config, "lean_lib").Select(table => (Table: table, Kind: "library"))
            .Concat(Tables(config, "lean_exe").Select(table => (Table: table, Kind: "executable")));
        foreach (var require in Tables(config, "require"))
        {
            var name = String(require, "name");
            var path = require.TryGetValue("path", out var raw) && raw is string relative
                ? Resolve("Reg", relative) : "";
            if (name == "leanInspector" || path == "tools/lean-inspector")
                edges.Add(new(Lakefile, $"require:{name}:{path}"));
        }
        foreach (var target in Strings(config, "defaultTargets", []))
            if (ImplementationModule(target.Split(':', '/')[0]) || target.StartsWith("leanInspector/", StringComparison.Ordinal))
                edges.Add(new(Lakefile, $"defaultTarget:{target}"));

        var pathsByModule = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var path in snapshot.Files.Keys.Where(p => p.Value.EndsWith(".lean", StringComparison.Ordinal)))
            pathsByModule[LeanImportClosure.ModuleName(path)] = path.Value;
        var packageSources = new HashSet<string>(StringComparer.Ordinal);
        var packageDirectory = Resolve("Reg", OptionalString(config, "srcDir", "."));
        foreach (var (library, kind) in targets)
        {
            var name = String(library, "name");
            var directory = Resolve(packageDirectory, OptionalString(library, "srcDir", "."));
            var roots = kind == "executable" ? [OptionalString(library, "root", name)]
                : Strings(library, "roots", [name]);
            var globs = kind == "executable" ? [] : Strings(library, "globs", [name + ".*"]);
            if (ImplementationModule(name) || directory == "tools/lean-inspector"
                || directory.StartsWith("tools/lean-inspector/", StringComparison.Ordinal))
                edges.Add(new(Lakefile, $"{kind}:{name}:{directory}"));
            var prefix = directory.Length == 0 ? "" : directory + "/";
            foreach (var path in snapshot.Files.Keys)
            {
                if (!path.Value.StartsWith(prefix, StringComparison.Ordinal)
                    || !path.Value.EndsWith(".lean", StringComparison.Ordinal)) continue;
                var module = path.Value[prefix.Length..^5].Replace('/', '.');
                if (!roots.Contains(module, StringComparer.Ordinal) && !globs.Any(glob => Matches(module, glob))) continue;
                pathsByModule[module] = path.Value;
                packageSources.Add(path.Value);
            }
        }

        var visited = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>(packageSources);
        while (pending.TryPop(out var path))
        {
            if (!visited.Add(path)) continue;
            if (!snapshot.TryGetFile(path, out var source))
                throw new FormatException($"missing package dependency source {path}");
            foreach (var import in LeanSourceCatalog.ParseFileImports(source))
            {
                var hasSource = pathsByModule.TryGetValue(import, out var dependency);
                if (ImplementationModule(import) || hasSource
                    && dependency!.StartsWith("tools/lean-inspector/", StringComparison.Ordinal))
                    edges.Add(new(path, $"import:{import}"));
                else if (hasSource)
                    pending.Push(dependency!);
                else if (import == "Reg" || import.StartsWith("Reg.", StringComparison.Ordinal)
                    || import.StartsWith("LeanInformationAuditInterface.", StringComparison.Ordinal)
                    || import.StartsWith("D5.", StringComparison.Ordinal))
                    throw new FormatException($"missing package dependency {import} imported by {path}");
            }
        }
        return edges;
    }

    private static bool ImplementationModule(string module) =>
        module is "LeanInformationAudit" or "LeanInformationAuditAnalysis"
            or "LeanInformationAuditRegTests" or "LeanInformationAuditRegAnalysis"
        || module.StartsWith("LeanInformationAudit.", StringComparison.Ordinal)
        || module.StartsWith("LeanInformationAuditAnalysis.", StringComparison.Ordinal)
        || module.StartsWith("LeanInformationAuditRegTests.", StringComparison.Ordinal)
        || module.StartsWith("LeanInformationAuditRegAnalysis.", StringComparison.Ordinal);

    private static bool Matches(string module, string glob) => glob.EndsWith(".*", StringComparison.Ordinal)
        ? module == glob[..^2] || module.StartsWith(glob[..^1], StringComparison.Ordinal)
        : glob.EndsWith(".+", StringComparison.Ordinal)
            ? module.StartsWith(glob[..^1], StringComparison.Ordinal) : module == glob;

    private static TomlTable[] Tables(TomlTable table, string key) =>
        !table.TryGetValue(key, out var value) ? [] : value switch
        {
            TomlTableArray array => array.ToArray(),
            TomlArray array when array.All(item => item is TomlTable) => array.Cast<TomlTable>().ToArray(),
            _ => throw new FormatException($"{key} must be an array of tables"),
        };

    private static string String(TomlTable table, string key) =>
        table.TryGetValue(key, out var value) && value is string { Length: > 0 } text
            ? text : throw new FormatException($"{key} must be a nonempty string");

    private static string OptionalString(TomlTable table, string key, string fallback) =>
        table.ContainsKey(key) ? String(table, key) : fallback;

    private static string[] Strings(TomlTable table, string key, string[] fallback) =>
        !table.TryGetValue(key, out var value) ? fallback
            : value is TomlArray array && array.All(item => item is string { Length: > 0 })
                ? array.Cast<string>().ToArray() : throw new FormatException($"{key} must be an array of strings");

    private static string Resolve(string directory, string relative)
    {
        if (relative.StartsWith("/", StringComparison.Ordinal) || relative.Contains('\\'))
            throw new FormatException("package source must be a repository-relative path");
        var parts = new List<string>();
        foreach (var part in (directory + "/" + relative).Split('/'))
        {
            if (part is "" or ".") continue;
            if (part == "..")
            {
                if (parts.Count == 0) throw new FormatException("package source escapes the repository");
                parts.RemoveAt(parts.Count - 1);
            }
            else parts.Add(part);
        }
        return string.Join('/', parts);
    }
}
