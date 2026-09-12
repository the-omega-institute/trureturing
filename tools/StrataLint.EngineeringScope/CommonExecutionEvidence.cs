using StrataLint.Engine;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.EngineeringScope;

internal sealed record TestProjectExecution(string Project, string InputFingerprint, string Status,
    string ExecutionCandidate, string ExecutionRound, string Results, int Exit, int Executed, string? Error);
internal sealed record RegisteredTestInput(string Project, string Assembly, string Fingerprint);
internal sealed record ExecutionMaterial(string Path, string Sha256);
internal sealed record TestExecutionRecord(int Version, string Candidate, string Round, TestProjectExecution[] Projects, ExecutionMaterial[] Materials);
internal sealed record StageStep(string Name, int RawExit, int Exit, string Status, string Log);
internal sealed record CommonStageRecord(int Version, string Candidate, string Round, StageStep[] Steps, ExecutionMaterial[] Materials, ResourcePlanBinding? Selection = null, string[]? Projects = null);
internal sealed record RegisteredCheckReport(string Producer, string Artifact, string[] Materials);
internal sealed record RegisteredCommonCheck(string Id, string[] ProgramProjects, string[] Materials,
    string[] MaterialExcludes, string[] PathInventory, RegisteredCheckReport[] ReportInputs);
internal sealed record CommonCheckManifest(string Schema, RegisteredCommonCheck[] Checks);

internal static partial class CommonExecutionEvidence
{
    internal const string RootPath = "build/ci";
    internal const string TestsPath = RootPath + "/tests.json";
    internal const string TestSeedPath = RootPath + "/test-seed";
    // Every change to invocation/acceptance semantics changes the project input identity.
    private const string TestContract = "registered-tests-v2;dotnet-test;Release;no-build;no-restore;unfiltered;trx;language=en-US";
    internal const string BuildPath = RootPath + "/build.json";
    internal const string EngineeringPath = RootPath + "/engineering.json";
    internal const string CurrentPath = RootPath + "/current.json";
    internal const string ScribeMarkdownPaths = RootPath + "/scribe-markdown.paths";
    internal const string CheckManifestPath = "Meta/ci-checks.json";
    internal const string ReportPath = ".lake/build/stratalint/raw-lean-report.json";
    internal static readonly string[] ReportPaths = [ReportPath, ReportPath + ".sha256", ReportPath + ".input.attestation",
        ReportPath + ".provenance.json", ReportPath + ".materials.zip", ReportPath + ".seed.json"];
    internal const string CliPath = "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll";
    internal const string RunnerPath = "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll";
    internal const string LeanProducerPath = "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll";
    internal const string ScribePath = "tools/StrataLint.Scribe.Documents/bin/Release/net10.0/StrataLint.Scribe.Documents.dll";
    internal static readonly string[] BuildSteps = ["restore-StrataLint", "build"];
    internal static readonly string[] EngineeringSteps = ["tests"];
    internal static readonly string[] CurrentSteps = ["lean-report", "scribe", "filemap", "check-current"];
    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower, UnmappedMemberHandling = System.Text.Json.Serialization.JsonUnmappedMemberHandling.Disallow, AllowDuplicateProperties = false, RespectRequiredConstructorParameters = true };

    internal static RepositorySnapshot Snapshot(string root) =>
        SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            _ => throw new InvalidDataException("candidate snapshot unavailable"),
        };

    internal static string Candidate(string root) => Candidate(root, out _);

    private static string Candidate(string root, out RepositorySnapshot snapshot)
    {
        snapshot = Snapshot(root);
        var files = snapshot.Files.Values.Select(file => new EngineeringSource(file.Path.Value, file.Text)).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        _ = registry.Sources(files);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var (path, file) in snapshot.Files.OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal))
        {
            hash.AppendData(Encoding.UTF8.GetBytes(path.Value + "\0"));
            var mode = OperatingSystem.IsWindows() ? 0 : (int)(File.GetUnixFileMode(Path.Combine(root, path.Value))
                & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute));
            hash.AppendData(Encoding.UTF8.GetBytes(mode == 0 ? "regular\0" : "executable\0"));
            hash.AppendData(SHA256.HashData(file.RawBytes.AsSpan()));
        }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    internal static IReadOnlyList<RegisteredCommonCheck> ReadCheckManifest(RepositorySnapshot snapshot,
        EngineeringProjectRegistry? registry = null)
    {
        if (!snapshot.TryGetFile(CheckManifestPath, out var file))
            throw new InvalidDataException($"missing common check registration: {CheckManifestPath}");
        CommonCheckManifest manifest;
        try
        {
            manifest = JsonSerializer.Deserialize<CommonCheckManifest>(file.Text, JsonOptions)
                ?? throw new InvalidDataException("empty common check registration");
        }
        catch (JsonException exception) { throw new InvalidDataException($"invalid common check registration: {exception.Message}", exception); }
        if (manifest.Schema != "ci-check-input-registration-v1" || manifest.Checks is null || manifest.Checks.Any(check => check is null))
            throw new InvalidDataException("invalid common check registration schema");
        var expected = new[] { "SL-001", "SL-002", "SL-003", "SL-004", "SL-006", "SL-008", "SL-010", "SL-011", "SL-012", "SL-015", "SL-017", "SL-018", "SL-019", "SL-020", "SL-021", "SL-023", "SL-025", "SL-026", "selftest-pair", "capability-proof", "banned-api-proof", "scribe-projections", "scribe-describe", "scribe-markdown", "filemap" };
        if (!manifest.Checks.Select(check => check.Id).Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
            throw new InvalidDataException("common check registration mismatch: missing=[" + string.Join(",", expected.Except(manifest.Checks.Select(check => check.Id)))
                + "] unexpected-or-duplicate=[" + string.Join(",", manifest.Checks.GroupBy(check => check.Id).Where(group => group.Count() != 1 || !expected.Contains(group.Key)).Select(group => group.Key)) + "]");
        registry ??= EngineeringProjectRegistry.Read(snapshot.Files.Values.Select(item => new EngineeringSource(item.Path.Value, item.Text)).ToArray());
        var projects = registry.Projects.Select(project => project.Path).ToHashSet(StringComparer.Ordinal);
        var paths = snapshot.Files.Keys.Select(path => path.Value).ToArray();
        foreach (var check in manifest.Checks)
        {
            if (check.ProgramProjects is null || check.Materials is null || check.MaterialExcludes is null
                || check.PathInventory is null || check.ReportInputs is null || check.ProgramProjects.Length == 0)
                throw new InvalidDataException($"missing common check registration fields: {check.Id}");
            foreach (var project in check.ProgramProjects)
                if (!projects.Contains(project)) throw new InvalidDataException($"check {check.Id} references unregistered project: {project}");
            ValidatePatterns(check.Materials, check.MaterialExcludes, check.Id);
            ValidatePatterns(check.PathInventory, [], check.Id);
            _ = EngineeringProjectRegistry.ExpandInputs(paths, check.Materials, check.MaterialExcludes, check.Id);
            _ = EngineeringProjectRegistry.ExpandInputs(paths, check.PathInventory, [], check.Id);
            if (check.ProgramProjects.Distinct(StringComparer.Ordinal).Count() != check.ProgramProjects.Length)
                throw new InvalidDataException("duplicate common check declaration: " + check.Id);
            var artifacts = new HashSet<string>(StringComparer.Ordinal);
            foreach (var report in check.ReportInputs)
            {
                if (report is null) throw new InvalidDataException("missing report declaration: " + check.Id);
                if (string.IsNullOrWhiteSpace(report.Producer) || report.Artifact is not ("raw-lean-report" or "VerifiedScribeEmissions")
                    || report.Materials is null || report.Materials.Length == 0)
                    throw new InvalidDataException($"invalid report input registration: {check.Id}: {report.Artifact}: {report.Producer}");
                if (!artifacts.Add(report.Artifact))
                    throw new InvalidDataException($"duplicate or conflicting report input: {check.Id}: {report.Artifact}: {report.Producer}");
                if (!snapshot.Files.ContainsKey(RepoPath.CreateKnown(report.Producer)))
                    throw new InvalidDataException($"check {check.Id} references missing producer: {report.Producer}");
                ValidatePatterns(report.Materials, [], check.Id);
                _ = EngineeringProjectRegistry.ExpandInputs(paths, report.Materials, [], check.Id);
            }
        }
        // Verified emissions come from the shared describe unit. Its registered
        // producer includes the Lean report consumed while emitting Scribe material.
        var describe = manifest.Checks.Single(check => check.Id == "scribe-describe");
        foreach (var check in manifest.Checks.Where(UsesScribe))
        {
            var input = check.ReportInputs.Single(report => report.Artifact == "VerifiedScribeEmissions");
            if (!check.Id.StartsWith("SL-", StringComparison.Ordinal)
                || !describe.ReportInputs.Any(report => report.Artifact == "raw-lean-report" && report.Producer == input.Producer))
                throw new InvalidDataException($"conflicting Scribe producer registration: {check.Id}: {input.Producer}: scribe-describe");
        }
        return manifest.Checks;

        static void ValidatePatterns(string[] patterns, string[] excludes, string id)
        {
            if (patterns.Any(pattern => string.IsNullOrWhiteSpace(pattern) || pattern.Contains(':'))
                || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length
                || excludes.Distinct(StringComparer.Ordinal).Count() != excludes.Length)
                throw new InvalidDataException($"invalid or duplicate common check input registration: {id}");
            foreach (var pattern in patterns.Concat(excludes)) _ = FileMapGlob.Create(pattern);
            foreach (var pattern in patterns.Where(pattern => !pattern.Contains('*')))
                if (excludes.Any(exclude => FileMapGlob.Create(exclude).IsMatch(pattern)))
                    throw new InvalidDataException($"conflicting common check input registration: {id}: {pattern}");
        }
    }

    private static bool UsesScribe(RegisteredCommonCheck check) =>
        check.ReportInputs.Any(report => report.Artifact == "VerifiedScribeEmissions");

    internal static string Hash(string path) => Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));

    internal static void Write<T>(string root, string path, T value)
    {
        var full = Path.Combine(root, path);
        Directory.CreateDirectory(Path.GetDirectoryName(full)!);
        File.WriteAllText(full + ".tmp", JsonSerializer.Serialize(value, JsonOptions) + "\n");
        File.Move(full + ".tmp", full, overwrite: true);
    }

    internal static T Read<T>(string root, string path) =>
        JsonSerializer.Deserialize<T>(File.ReadAllText(Path.Combine(root, path)), JsonOptions)
        ?? throw new InvalidDataException($"missing evidence {path}");

    internal static ExecutionMaterial[] Materials(string root, IEnumerable<string> paths) =>
        paths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).Select(path => new ExecutionMaterial(path, Hash(Path.Combine(root, path)))).ToArray();

    internal static CommonStageRecord SealBuild(string root, string candidate, IEnumerable<string> binaries, StageStep[] steps, string[]? projects = null, ResourcePlanBinding? selection = null)
    {
        RequirePassed(steps, projects is null ? BuildSteps : projects.SelectMany(_ => BuildSteps).ToArray());
        if (candidate != Candidate(root)) throw new InvalidDataException("candidate changed during build");
        var round = Guid.NewGuid().ToString("N");
        var record = new CommonStageRecord(2, candidate, round, steps,
            Materials(root, binaries.Concat(steps.Select(step => step.Log)).Concat(SelectionPaths(selection))), selection, projects);
        Write(root, BuildPath, record);
        WriteBundleList(root, "build", record.Materials.Select(material => material.Path).Append(BuildPath));
        return record;
    }

    internal static CommonStageRecord ValidateBuild(string root, string? round = null) =>
        ValidateBuild(root, Candidate(root), round);

    private static CommonStageRecord ValidateBuild(string root, string candidate, string? round)
    {
        var record = Read<CommonStageRecord>(root, BuildPath);
        if (string.IsNullOrWhiteSpace(record.Round)) throw new InvalidDataException("missing build round");
        ValidateRecord(root, record, candidate, round ?? record.Round);
        RequirePassed(record.Steps, record.Projects is null ? BuildSteps : record.Projects.SelectMany(_ => BuildSteps).ToArray());
        if (record.Projects is { Length: 0 }) throw new InvalidDataException("empty build project selection");
        if (record.Selection is not null)
        {
            if (SelectionPaths(record.Selection).Any(path => !record.Materials.Any(material => material.Path == path)))
                throw new InvalidDataException("build has missing resource selection materials");
            var plan = ResourceExecutionPlan.Load(root, Path.Combine(root, record.Selection.Plan), Path.Combine(root, record.Selection.Changes))!;
            if (record.Projects is null || !record.Projects.SequenceEqual(plan.Projects)) throw new InvalidDataException("build differs from declared resource projects");
        }
        else if (record.Projects is not null && !record.Projects.SequenceEqual(
                     EngineeringProjectRegistry.Read(Snapshot(root)).Projects.Where(project => project.Ci).Select(project => project.Path).Order(StringComparer.Ordinal)))
            throw new InvalidDataException("default build differs from registered CI projects");
        return record;
    }

    internal static void ValidateStartedBuild(string root, CommonStageRecord started, string candidate)
    {
        var completed = ValidateBuild(root, candidate, started.Round);
        if (started.Candidate != candidate || !completed.Steps.SequenceEqual(started.Steps) || !completed.Materials.SequenceEqual(started.Materials))
            throw new InvalidDataException("build receipt changed during branch execution");
    }

    internal static void SealEngineering(string root, CommonStageRecord build, StageStep[] steps)
    {
        RequirePassed(steps, EngineeringSteps);
        var candidate = Candidate(root, out var snapshot);
        ValidateStartedBuild(root, build, candidate);
        var tests = ValidateTests(root, Read<TestExecutionRecord>(root, TestsPath), candidate, snapshot);
        if (tests.Round != build.Round) throw new InvalidDataException("tests belong to a different build round");
        var checks = ValidateChecks(root, "engineering", build);
        var record = new CommonStageRecord(2, candidate, build.Round, steps,
            Materials(root, new[] { BuildPath, TestsPath, ChecksPath("engineering") }.Concat(checks.Units.SelectMany(unit => unit.Materials).Select(material => material.Path)).Concat(tests.Materials.Select(material => material.Path))
                .Concat(steps.Select(step => step.Log))));
        Write(root, EngineeringPath, record);
        // The consumer already has the shared build (directly, or in current's
        // standalone release bundle). Engineering transports only its own work.
        WriteBundleList(root, "engineering", record.Materials.Select(material => material.Path)
            .Where(path => path != BuildPath).Append(EngineeringPath));
    }

    internal static CommonStageRecord ValidateEngineering(string root)
    {
        var candidate = Candidate(root, out var snapshot);
        return ValidateEngineering(root, ValidateBuild(root, candidate, null), snapshot);
    }

    private static CommonStageRecord ValidateEngineering(string root, CommonStageRecord build,
        RepositorySnapshot snapshot, IEnumerable<string>? baseProjects = null)
    {
        var tests = ValidateTests(root, Read<TestExecutionRecord>(root, TestsPath), build.Candidate, snapshot, baseProjects);
        if (tests.Round != build.Round) throw new InvalidDataException("tests belong to a different build round");
        var record = Read<CommonStageRecord>(root, EngineeringPath);
        ValidateRecord(root, record, build.Candidate, build.Round);
        RequirePassed(record.Steps, EngineeringSteps);
        _ = ValidateChecks(root, "engineering", build);
        if (!record.Materials.Any(material => material.Path == ChecksPath("engineering")))
            throw new InvalidDataException("engineering has no bound common check evidence");
        if (!record.Materials.Any(material => material.Path == TestsPath)
            || !record.Materials.Any(material => material.Path == BuildPath))
            throw new InvalidDataException("engineering has no bound test or build evidence");
        return record;
    }

    internal static (CommonStageRecord Current, CommonStageRecord Engineering, CommonStageRecord Build) ValidateCommon(
        string root, IEnumerable<string>? baseProjects = null)
    {
        var candidate = Candidate(root, out var snapshot);
        var build = ValidateBuild(root, candidate, null);
        var engineering = ValidateEngineering(root, build, snapshot, baseProjects);
        return (ValidateCurrent(root, build, snapshot), engineering, build);
    }

    private static void ValidateRecord(string root, CommonStageRecord record, string candidate, string round)
    {
        if (record.Version != 2 || record.Candidate != candidate || record.Round != round)
            throw new InvalidDataException("common evidence candidate identity or round mismatch");
        RequirePassed(record.Steps);
        ValidateMaterials(root, record.Materials);
        if (record.Steps.Any(step => !record.Materials.Any(material => material.Path == step.Log)))
            throw new InvalidDataException("common step has no bound operation log");
    }

    private static void RequirePassed(IEnumerable<StageStep> steps, string[]? required = null)
    {
        if (steps.Any(step => step.Exit != 0 || !(step.Status == "executed"
                || step.Status == "reused" && step.Name is "scribe" or "filemap" or "check-current")
                || step.RawExit != (step.Name is "capability-proof" or "banned-api-proof" ? 1 : 0)))
            throw new InvalidDataException("required common step did not succeed");
        if (required is not null && !required.SequenceEqual(steps.Select(step => step.Name)))
            throw new InvalidDataException("required common steps are missing, duplicated, or out of order");
    }

    internal static string BundleListPath(string stage) => RootPath + "/" + stage + "-paths.nul";

    private static void WriteBundleList(string root, string stage, IEnumerable<string> materials) =>
        File.WriteAllText(Path.Combine(root, BundleListPath(stage)),
            string.Join('\0', CanonicalBundlePaths(root, stage, materials)) + "\0");

    internal static string[] CanonicalBundlePaths(string root, string stage, IEnumerable<string> materials)
    {
        var paths = materials.ToArray();
        var logs = new[] { RootPath + "/logs/" + stage }.Concat(stage == "current" && paths.Contains(ReportPath) ? [ReportPath + ".logs"] : [])
            .Where(directory => Directory.Exists(Path.Combine(root, directory)));
        return paths.Concat(logs).Append(BundleListPath(stage)).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
    }

    internal static void ValidateMaterials(string root, IEnumerable<ExecutionMaterial> materials)
    {
        foreach (var material in materials)
        {
            if (!RepoPath.TryCreate(material.Path, out _) || Hash(Path.Combine(root, material.Path)) != material.Sha256)
                throw new InvalidDataException($"artifact integrity mismatch: {material.Path}");
        }
    }

}
