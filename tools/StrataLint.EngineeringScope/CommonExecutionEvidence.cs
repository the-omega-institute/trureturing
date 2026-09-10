using StrataLint.Engine;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record TestProjectExecution(string Project, string Results, int Exit, int Executed, string? Error);
internal sealed record ExecutionMaterial(string Path, string Sha256);
internal sealed record TestExecutionRecord(int Version, string Candidate, string Round, TestProjectExecution[] Projects, ExecutionMaterial[] Materials);
internal sealed record StageStep(string Name, int RawExit, int Exit, string Status, string Log);
internal sealed record CommonStageRecord(int Version, string Candidate, string Round, StageStep[] Steps, ExecutionMaterial[] Materials);

internal static class CommonExecutionEvidence
{
    internal const string RootPath = "build/ci";
    internal const string TestsPath = RootPath + "/tests.json";
    internal const string BuildPath = RootPath + "/build.json";
    internal const string EngineeringPath = RootPath + "/engineering.json";
    internal const string CurrentPath = RootPath + "/current.json";
    internal const string ReportPath = ".lake/build/stratalint/raw-lean-report.json";
    internal static readonly string[] ReportPaths = [ReportPath, ReportPath + ".sha256", ReportPath + ".input.attestation",
        ReportPath + ".provenance.json", ReportPath + ".materials.zip", ReportPath + ".seed.json"];
    internal const string CliPath = "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll";
    internal const string RunnerPath = "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll";
    internal const string ScribePath = "tools/StrataLint.Scribe.Documents/bin/Release/net10.0/StrataLint.Scribe.Documents.dll";
    internal static readonly string[] BuildSteps = ["restore-StrataLint", "build"];
    internal static readonly string[] EngineeringSteps = ["restore-CompileFailProof", "restore-BannedApiCompileFailProof", "tests", "selftest-first", "selftest-second", "capability-proof", "banned-api-proof"];
    internal static readonly string[] CurrentSteps = ["lean-report", "scribe", "filemap", "check-current"];
    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower, UnmappedMemberHandling = System.Text.Json.Serialization.JsonUnmappedMemberHandling.Disallow };

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
        var projects = snapshot.Files.Keys.Select(path => path.Value)
            .Where(path => path.EndsWith(".csproj", StringComparison.Ordinal)).ToArray();
        if (projects.Length != 0)
        {
            var compile = MsBuildCompileOracle.Query(root, projects, configuration: "Release");
            if (compile.Findings.Count != 0)
                throw new InvalidDataException(string.Join("\n", compile.Findings.Select(finding => finding.Message)));
            foreach (var path in compile.ProjectBySourcePath.Keys)
                if (!snapshot.TryGetFile(path, out _))
                    throw new InvalidDataException($"Compile input is absent from candidate source: {path}");
        }
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

    internal static CommonStageRecord SealBuild(string root, string candidate, IEnumerable<string> binaries, StageStep[] steps)
    {
        RequirePassed(steps, BuildSteps);
        var products = binaries.Concat(CommonCompileMetadata.Export(root, Snapshot(root))).ToArray();
        if (candidate != Candidate(root)) throw new InvalidDataException("candidate changed during build");
        var record = new CommonStageRecord(1, candidate, Guid.NewGuid().ToString("N"), steps,
            Materials(root, products.Concat(steps.Select(step => step.Log))));
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
        RequirePassed(record.Steps, BuildSteps);
        _ = CommonCompileMetadata.Load(root, record.Materials);
        return record;
    }

    private static void ValidateStartedBuild(string root, CommonStageRecord started, string candidate)
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
        var record = new CommonStageRecord(1, candidate, build.Round, steps,
            Materials(root, new[] { BuildPath, TestsPath }.Concat(tests.Materials.Select(material => material.Path))
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
        if (!record.Materials.Any(material => material.Path == TestsPath)
            || !record.Materials.Any(material => material.Path == BuildPath))
            throw new InvalidDataException("engineering has no bound test or build evidence");
        return record;
    }

    internal static void SealCurrent(string root, CommonStageRecord build, StageStep[] steps)
    {
        var candidate = Candidate(root, out var snapshot);
        ValidateStartedBuild(root, build, candidate);
        RequirePassed(steps, CurrentSteps);
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
        var record = new CommonStageRecord(1, build.Candidate, build.Round, steps,
            Materials(root, ReportPaths.Append(BuildPath).Concat(steps.Select(step => step.Log))));
        Write(root, CurrentPath, record);
        WriteBundleList(root, "current", build.Materials.Concat(record.Materials)
            .Select(material => material.Path).Append(CurrentPath));
    }

    internal static CommonStageRecord ValidateCurrent(string root)
    {
        var candidate = Candidate(root, out var snapshot);
        return ValidateCurrent(root, ValidateBuild(root, candidate, null), snapshot);
    }

    private static CommonStageRecord ValidateCurrent(string root, CommonStageRecord build, RepositorySnapshot snapshot)
    {
        var record = Read<CommonStageRecord>(root, CurrentPath);
        ValidateRecord(root, record, build.Candidate, build.Round);
        RequirePassed(record.Steps, CurrentSteps);
        if (ReportPaths.Any(path => !record.Materials.Any(material => material.Path == path))
            || !record.Materials.Any(material => material.Path == BuildPath))
            throw new InvalidDataException("current has no bound report or build evidence");
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
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
        if (record.Version != 1 || record.Candidate != candidate || record.Round != round)
            throw new InvalidDataException("common evidence candidate identity or round mismatch");
        RequirePassed(record.Steps);
        ValidateMaterials(root, record.Materials);
    }

    private static void RequirePassed(IEnumerable<StageStep> steps, string[]? required = null)
    {
        if (steps.Any(step => step.Exit != 0 || step.Status != "executed"
                || step.RawExit != (step.Name is "capability-proof" or "banned-api-proof" ? 1 : 0)))
            throw new InvalidDataException("required common step did not succeed");
        if (required is not null && !required.SequenceEqual(steps.Select(step => step.Name)))
            throw new InvalidDataException("required common steps are missing, duplicated, or out of order");
    }

    internal static string BundleListPath(string stage) => RootPath + "/" + stage + "-paths.nul";

    private static void WriteBundleList(string root, string stage, IEnumerable<string> materials)
    {
        var path = BundleListPath(stage);
        var logs = new[] { RootPath + "/logs/" + stage }.Concat(stage == "current" ? [ReportPath + ".logs"] : [])
            .Where(directory => Directory.Exists(Path.Combine(root, directory)));
        File.WriteAllText(Path.Combine(root, path), string.Join('\0', materials.Concat(logs).Append(path)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)) + "\0");
    }

    internal static void ValidateMaterials(string root, IEnumerable<ExecutionMaterial> materials)
    {
        foreach (var material in materials)
        {
            if (!RepoPath.TryCreate(material.Path, out _) || Hash(Path.Combine(root, material.Path)) != material.Sha256)
                throw new InvalidDataException($"artifact integrity mismatch: {material.Path}");
        }
    }

    internal static TestExecutionRecord ValidateTests(string root, IEnumerable<string>? requiredProjects = null)
    {
        var record = Read<TestExecutionRecord>(root, TestsPath);
        var candidate = Candidate(root, out var snapshot);
        return ValidateTests(root, record, candidate, snapshot, requiredProjects);
    }

    private static TestExecutionRecord ValidateTests(string root, TestExecutionRecord record, string candidate,
        RepositorySnapshot snapshot, IEnumerable<string>? requiredProjects = null)
    {
        if (record.Version != 1 || record.Candidate != candidate || string.IsNullOrWhiteSpace(record.Round))
            throw new InvalidDataException("engineering evidence candidate identity mismatch or invalid version/round");
        ValidateMaterials(root, record.Materials);
        var expected = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot));
        if (expected.Length == 0 || !expected.SequenceEqual(record.Projects.Select(static result => result.Project)))
            throw new InvalidDataException("engineering evidence does not cover every current test project exactly once");
        foreach (var project in record.Projects)
        {
            if (project.Exit != 0 || project.Error is not null || project.Executed <= 0)
                throw new InvalidDataException($"test project failed: {project.Project}: {project.Error}");
            if (!RepoPath.TryCreate(project.Results, out _)) throw new InvalidDataException("invalid TRX path");
            var directory = Path.Combine(root, project.Results);
            var files = Directory.GetFiles(directory, "*.trx").Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).ToArray();
            if (files.Length == 0 || files.Any(path => !record.Materials.Any(material => material.Path == path)))
                throw new InvalidDataException($"missing bound TRX material for {project.Project}");
            if (TestResultEvidence.Load(directory).Executed != project.Executed)
                throw new InvalidDataException($"TRX count mismatch: {project.Project}");
        }
        foreach (var project in requiredProjects ?? [])
            if (!record.Projects.Any(result => result.Project == project && result.Exit == 0 && result.Executed > 0))
                throw new InvalidDataException($"base test project has no successful candidate execution: {project}");
        return record;
    }
}
