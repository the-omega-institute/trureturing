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
    internal const string EngineeringPath = RootPath + "/engineering.json";
    internal const string CurrentPath = RootPath + "/current.json";
    internal const string ReportPath = ".lake/build/stratalint/raw-lean-report.json";
    internal static readonly string[] ReportPaths = [ReportPath, ReportPath + ".sha256", ReportPath + ".input.attestation",
        ReportPath + ".provenance.json", ReportPath + ".materials.zip", ReportPath + ".seed.json"];
    internal const string CliPath = "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll";
    internal const string RunnerPath = "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll";
    internal const string ScribePath = "tools/StrataLint.Scribe.Documents/bin/Release/net10.0/StrataLint.Scribe.Documents.dll";
    internal static readonly string[] EngineeringSteps = ["restore-StrataLint", "restore-CompileFailProof", "restore-BannedApiCompileFailProof", "build", "tests", "selftest-first", "selftest-second", "capability-proof", "banned-api-proof"];
    internal static readonly string[] CurrentSteps = ["lean-report", "scribe", "filemap", "check-current"];
    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower, UnmappedMemberHandling = System.Text.Json.Serialization.JsonUnmappedMemberHandling.Disallow };

    internal static RepositorySnapshot Snapshot(string root) =>
        SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidDataException(failure.Message),
            _ => throw new InvalidDataException("candidate snapshot unavailable"),
        };

    internal static string Candidate(string root)
    {
        var snapshot = Snapshot(root);
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

    internal static void SealEngineering(string root, IEnumerable<string> binaries, StageStep[] steps)
    {
        var tests = ValidateTests(root);
        RequirePassed(steps, EngineeringSteps);
        var products = binaries.Concat(CommonCompileMetadata.Export(root, Snapshot(root))).ToArray();
        Write(root, EngineeringPath, new CommonStageRecord(1, tests.Candidate, tests.Round, steps,
            Materials(root, products.Concat([TestsPath]).Concat(steps.Select(step => step.Log)))));
        WriteBundleList(root, products);
    }

    internal static CommonStageRecord ValidateEngineering(string root)
    {
        var tests = ValidateTests(root);
        var record = Read<CommonStageRecord>(root, EngineeringPath);
        ValidateRecord(root, record, tests.Candidate, tests.Round);
        RequirePassed(record.Steps, EngineeringSteps);
        if (!record.Materials.Any(material => material.Path == TestsPath)) throw new InvalidDataException("engineering has no bound test evidence");
        _ = CommonCompileMetadata.Load(root, record.Materials);
        return record;
    }

    internal static void SealCurrent(string root, StageStep[] steps)
    {
        var engineering = ValidateEngineering(root);
        RequirePassed(steps, CurrentSteps);
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), Snapshot(root), validateMaterials: true);
        Write(root, CurrentPath, new CommonStageRecord(1, engineering.Candidate, engineering.Round, steps,
            Materials(root, ReportPaths.Append(EngineeringPath).Concat(steps.Select(step => step.Log)))));
        var logs = Path.Combine(root, ReportPath + ".logs");
        WriteBundleList(root, engineering.Materials.Select(material => material.Path).Concat(ReportPaths)
            .Concat(Directory.Exists(logs) ? [ReportPath + ".logs"] : []));
    }

    internal static CommonStageRecord ValidateCurrent(string root, IEnumerable<string>? baseProjects = null)
    {
        var engineering = ValidateEngineering(root);
        ValidateTests(root, baseProjects);
        var record = Read<CommonStageRecord>(root, CurrentPath);
        ValidateRecord(root, record, engineering.Candidate, engineering.Round);
        RequirePassed(record.Steps, CurrentSteps);
        if (ReportPaths.Any(path => !record.Materials.Any(material => material.Path == path))
            || !record.Materials.Any(material => material.Path == EngineeringPath))
            throw new InvalidDataException("current has no bound report or engineering evidence");
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), Snapshot(root), validateMaterials: true);
        return record;
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
        if (steps.Any(step => step.Exit != 0 || step.Status != "executed"))
            throw new InvalidDataException("required common step did not succeed");
        if (required is not null && !required.SequenceEqual(steps.Select(step => step.Name)))
            throw new InvalidDataException("required common steps are missing, duplicated, or out of order");
    }

    private static void WriteBundleList(string root, IEnumerable<string> materials) =>
        File.WriteAllText(Path.Combine(root, RootPath, "artifact-paths.nul"), string.Join('\0',
            materials.Where(path => !path.StartsWith(RootPath + "/", StringComparison.Ordinal)).Append(RootPath).Distinct().Order(StringComparer.Ordinal)) + "\0");

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
        if (record.Version != 1 || record.Candidate != Candidate(root) || string.IsNullOrWhiteSpace(record.Round))
            throw new InvalidDataException("engineering evidence candidate identity mismatch or invalid version/round");
        ValidateMaterials(root, record.Materials);
        var expected = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(Snapshot(root)));
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
