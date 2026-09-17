using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class InformationTemplateHistoryBundle
{
    internal const string ReportName = "raw-lean-report.json";
    internal static readonly string[] Suffixes = ["", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip"];

    internal static void Seal(string directory, string producer, string revision, RepositorySnapshot hybrid,
        string candidate, string run)
    {
        var coordinates = ValidateReport(Path.Combine(directory, ReportName), hybrid);
        var members = Suffixes.ToDictionary(s => ReportName + s, s => Digest(Path.Combine(directory, ReportName + s)));
        var metadata = JsonSerializer.SerializeToElement(new
        {
            schema = "information-template-history-bundle-v1", producer, revision,
            pair = InformationTemplateHistoryPlan.Target(producer, revision, "local", "local").Pair,
            hybrid_input = coordinates.Repository, toolchain = hybrid.Files[RepoPath.CreateKnown("lean-toolchain")].Text,
            producer_commit = candidate, producer_run = run, members,
        });
        File.WriteAllBytes(Path.Combine(directory, "history.json"), InformationTemplateJson.Canonical(metadata).AsSpan());
    }

    internal static void Validate(string directory, string producer, string revision, RepositorySnapshot hybrid)
    {
        var history = Path.Combine(directory, "history.json");
        RequireFile(history);
        using var document = InformationTemplateJson.Read(File.ReadAllBytes(history));
        var value = document.RootElement;
        InformationTemplateJson.Fields(value, "schema", "producer", "revision", "pair", "hybrid_input", "toolchain",
            "producer_commit", "producer_run", "members");
        var coordinates = InformationTemplateHistoryInputs.Coordinates(hybrid);
        if (Text(value, "schema") != "information-template-history-bundle-v1" || Text(value, "producer") != producer
            || Text(value, "revision") != revision || Text(value, "hybrid_input") != coordinates.Repository
            || Text(value, "pair") != InformationTemplateHistoryPlan.Target(producer, revision, "local", "local").Pair
            || Text(value, "toolchain") != hybrid.Files[RepoPath.CreateKnown("lean-toolchain")].Text)
            throw new FormatException("history bundle identity differs from fresh P/R/H");
        InformationTemplateJson.Hash(Text(value, "producer_commit"), 40);
        Text(value, "producer_run");
        var members = value.GetProperty("members");
        InformationTemplateJson.Fields(members, Suffixes.Select(s => ReportName + s).ToArray());
        foreach (var suffix in Suffixes)
        {
            var path = Path.Combine(directory, ReportName + suffix);
            RequireFile(path);
            if (Text(members, ReportName + suffix) != Digest(path))
                throw new FormatException("history member digest mismatch: " + suffix);
        }
        ValidateReport(Path.Combine(directory, ReportName), hybrid);
    }

    internal static InformationTemplateHistoryCoordinates ValidateReport(string reportPath, RepositorySnapshot hybrid)
    {
        foreach (var suffix in Suffixes) RequireFile(reportPath + suffix);
        var sha = Digest(reportPath);
        if (File.ReadAllText(reportPath + ".sha256") != sha + "  " + Path.GetFileName(reportPath) + "\n")
            throw new FormatException("history report checksum mismatch");
        var coordinates = InformationTemplateHistoryInputs.Coordinates(hybrid);
        var attestation = "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={coordinates.Repository}\nproducer_sha256={coordinates.Compatibility}\nreport_sha256={sha}\n";
        if (File.ReadAllText(reportPath + ".input.attestation") != attestation)
            throw new FormatException("history report input attestation differs from H");
        using var provenance = ReadJson(reportPath + ".provenance.json");
        var value = provenance.RootElement;
        InformationTemplateJson.Fields(value, "schema", "side", "mode", "source_side", "input_address", "producer_sha256",
            "repository_inspector_sha256", "lean_sources_sha256", "lean_config_sha256", "report_sha256", "module_origins");
        if (Text(value, "schema") != "stratalint-lean-report-provenance-v2" || Text(value, "side") != "candidate"
            || Text(value, "source_side") != "candidate" || Text(value, "mode") is not ("produced" or "cached")
            || Text(value, "report_sha256") != sha || Text(value, "input_address") != "sha256:" + coordinates.Input
            || Text(value, "producer_sha256") != coordinates.Compatibility
            || Text(value, "repository_inspector_sha256") != coordinates.Compatibility
            || Text(value, "lean_sources_sha256") != coordinates.Sources || Text(value, "lean_config_sha256") != coordinates.Config)
            throw new FormatException("history provenance differs from H");
        var report = RawLeanReportArtifact.ReadFile(reportPath, hybrid);
        InformationTemplateEvidence.Collect(hybrid, report);
        ValidateMaterials(reportPath, report);
        using var raw = ReadJson(reportPath);
        var rows = raw.RootElement.GetProperty("modules").EnumerateArray().ToArray();
        var origins = value.GetProperty("module_origins");
        InformationTemplateJson.Fields(origins, rows.Select(row => Text(row, "module")).ToArray());
        var files = hybrid.Files.Values.ToDictionary(f => f.Path.Value, f => new RawRepositoryEntry(f.Path.Value, f.RawBytes));
        var allowed = InformationTemplateHistoryInputs.Select(files, "report_modules")
            .Concat(InformationTemplateHistoryInputs.Select(files, "dependency_sources")).ToHashSet(StringComparer.Ordinal);
        var hashes = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var row in rows)
        {
            var module = Text(row, "module");
            var origin = origins.GetProperty(module);
            InformationTemplateJson.Fields(origin, "module", "report_sha256", "compatibility_sha256",
                "producer_sources_sha256", "inspector_executable_sha256", "input_sources");
            var moduleBytes = StructuredCanonicalWriter.WriteJson(JsonSerializer.SerializeToElement(new
                { schema = RawLeanReportArtifact.Schema, modules = new[] { row } }));
            if (Text(origin, "module") != module || Text(origin, "compatibility_sha256") != coordinates.Compatibility
                || Text(origin, "report_sha256") != InformationTemplateJson.Sha256(moduleBytes.AsSpan()))
                throw new FormatException("history module provenance mismatch: " + module);
            InformationTemplateJson.Hash(Text(origin, "producer_sources_sha256"), 64);
            InformationTemplateJson.Hash(Text(origin, "inspector_executable_sha256"), 64);
            var bindings = origin.GetProperty("input_sources");
            if (Text(bindings, Text(row, "source_path")) != Text(row, "source_sha256")[7..])
                throw new FormatException("history origin omitted its module source");
            foreach (var binding in bindings.EnumerateObject())
            {
                if (!allowed.Contains(binding.Name) || !files.TryGetValue(binding.Name, out var input))
                    throw new FormatException("history origin has unregistered source: " + binding.Name);
                if (!hashes.TryGetValue(binding.Name, out var digest))
                    hashes.Add(binding.Name, digest = InformationTemplateJson.Sha256(input.Bytes.AsSpan()));
                if (binding.Value.GetString() != digest)
                    throw new FormatException("history origin source differs from H: " + binding.Name);
            }
        }
        return coordinates;
    }

    private static void ValidateMaterials(string reportPath, LeanAxiomReport report)
    {
        var expected = report.Files.Values.SelectMany(f => f.Declarations).Select(d => "sha256/" + d.StatementTypeAddress[7..])
            .ToHashSet(StringComparer.Ordinal);
        using var archive = ZipFile.OpenRead(reportPath + ".materials.zip");
        if (archive.Entries.Count != expected.Count || !expected.SetEquals(archive.Entries.Select(e => e.FullName))
            || archive.Entries.Any(e => e.Name.Length == 0 || (e.ExternalAttributes >> 16 & 0xf000) is not (0 or 0x8000)))
            throw new FormatException("history materials contain missing, duplicate or nonregular members");
        foreach (var (path, module) in report.Files)
        foreach (var declaration in module.Declarations)
        {
            var material = declaration.LoadTypeRepresentation();
            var computed = new LeanDeclaration(declaration.Name, declaration.Kind, material, declaration.Axioms)
                { NameKey = declaration.NameKey };
            if (computed.StatementTypeAddress != declaration.StatementTypeAddress
                || CanonicalStatementWriter.DeclarationStatementId(path, computed) != declaration.PrecomputedStatementId)
                throw new FormatException("history declaration material identity mismatch: " + declaration.Name);
        }
    }

    internal static void Copy(string report, string directory)
    {
        Directory.CreateDirectory(directory);
        foreach (var suffix in Suffixes) File.Copy(report + suffix, Path.Combine(directory, ReportName + suffix), true);
        File.WriteAllText(Path.Combine(directory, ReportName + ".sha256"), Digest(report) + "  " + ReportName + "\n");
    }

    internal static string Digest(string path)
    {
        using var source = File.OpenRead(path);
        return Convert.ToHexStringLower(SHA256.HashData(source));
    }

    internal static void RequireFile(string path)
    {
        var full = LeanCacheGuard.PhysicalPath(path);
        for (var parent = new FileInfo(full).Directory; parent is not null; parent = parent.Parent)
            if (parent.LinkTarget is not null) throw new IOException("history bundle traverses a symlink: " + path);
        var info = new FileInfo(full);
        if (!info.Exists || info.Length == 0 || info.LinkTarget is not null || (info.Attributes & FileAttributes.ReparsePoint) != 0)
            throw new IOException("history bundle missing or nonregular member: " + path);
    }

    private static JsonDocument ReadJson(string path)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(path));
        return JsonDocument.Parse(InformationTemplateJson.Canonical(document.RootElement).AsMemory());
    }

    private static string Text(JsonElement value, string name) => InformationTemplateJson.String(value, name);
}
