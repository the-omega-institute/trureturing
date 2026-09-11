using StrataLint.Engine;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record TestProjectExecution(string Project, string Results, int Exit, int Executed, string? Error)
{
    public TestActionCoverage[] Coverage { get; init; } = [];
}
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
    internal const string LeanProducerPath = "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll";
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

    private static string Candidate(string root, out RepositorySnapshot snapshot) => Candidate(root, out snapshot, out _);

    private static string Candidate(string root, out RepositorySnapshot snapshot, out Dictionary<string, ActionInput> inputs)
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
        inputs = new(StringComparer.Ordinal);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var (path, file) in snapshot.Files.OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal))
        {
            hash.AppendData(Encoding.UTF8.GetBytes(path.Value + "\0"));
            var mode = OperatingSystem.IsWindows() ? 0 : (int)(File.GetUnixFileMode(Path.Combine(root, path.Value))
                & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute));
            hash.AppendData(Encoding.UTF8.GetBytes(mode == 0 ? "regular\0" : "executable\0"));
            var digest = SHA256.HashData(file.RawBytes.AsSpan());
            inputs.Add(path.Value, new(path.Value, Convert.ToHexStringLower(digest)));
            hash.AppendData(digest);
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
        var clock = TimeProvider.System;
        var started = clock.GetTimestamp();
        RequirePassed(steps, BuildSteps);
        var completed = Candidate(root, out var snapshot, out var inputs);
        var candidateFinished = clock.GetTimestamp();
        if (candidate != completed) throw new InvalidDataException("candidate changed during build");
        var materials = Materials(root, binaries.Concat(steps.Select(step => step.Log)));
        var hashFinished = clock.GetTimestamp();
        materials = materials.Concat(Materials(root, CommonCompileMetadata.Export(root, snapshot, materials)))
            .OrderBy(item => item.Path, StringComparer.Ordinal).ToArray();
        var metadataFinished = clock.GetTimestamp();
        var planFinished = metadataFinished;
        var serializationFinished = metadataFinished;
        if (materials.Any(material => material.Path == AffectedTestPlan.NativePath))
        {
            var plan = AffectedTestPlan.Derive(root, candidate, snapshot, inputs, materials);
            planFinished = clock.GetTimestamp();
            Write(root, AffectedTestPlan.PathName, plan);
            serializationFinished = clock.GetTimestamp();
            materials = materials.Concat(Materials(root, [AffectedTestPlan.PathName])).OrderBy(item => item.Path, StringComparer.Ordinal).ToArray();
        }
        var record = new CommonStageRecord(1, candidate, Guid.NewGuid().ToString("N"), steps, materials);
        Write(root, BuildPath, record);
        WriteBundleList(root, "build", record.Materials.Select(material => material.Path).Append(BuildPath));
        Write(root, RootPath + "/seal-cost.json", new {
            candidate_seconds = clock.GetElapsedTime(started, candidateFinished).TotalSeconds,
            material_hash_seconds = clock.GetElapsedTime(candidateFinished, hashFinished).TotalSeconds,
            compile_metadata_seconds = clock.GetElapsedTime(hashFinished, metadataFinished).TotalSeconds,
            plan_seconds = clock.GetElapsedTime(metadataFinished, planFinished).TotalSeconds,
            serialization_seconds = clock.GetElapsedTime(planFinished, serializationFinished).TotalSeconds,
            seal_seconds = clock.GetElapsedTime(started).TotalSeconds });
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

    private static CommonStageRecord ValidateStartedBuild(string root, CommonStageRecord started, string candidate)
    {
        var completed = ValidateBuild(root, candidate, started.Round);
        if (started.Candidate != candidate || !completed.Steps.SequenceEqual(started.Steps) || !completed.Materials.SequenceEqual(started.Materials))
            throw new InvalidDataException("build receipt changed during branch execution");
        return completed;
    }

    internal static void SealEngineering(string root, CommonStageRecord build, StageStep[] steps)
    {
        RequirePassed(steps, EngineeringSteps);
        var candidate = Candidate(root, out var snapshot);
        var validatedBuild = ValidateStartedBuild(root, build, candidate);
        var tests = ValidateTests(root, Read<TestExecutionRecord>(root, TestsPath), candidate, snapshot, build: validatedBuild);
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
        var tests = ValidateTests(root, Read<TestExecutionRecord>(root, TestsPath), build.Candidate, snapshot, baseProjects, build);
        if (tests.Round != build.Round) throw new InvalidDataException("tests belong to a different build round");
        var record = Read<CommonStageRecord>(root, EngineeringPath);
        ValidateRecord(root, record, build.Candidate, build.Round);
        RequirePassed(record.Steps, EngineeringSteps);
        if ((record.Steps.Single(step => step.Name == "tests").Status == "reused") != tests.Projects.All(project => project.Executed == 0))
            throw new InvalidDataException("tests stage status disagrees with current coverage");
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
        if (steps.Any(step => step.Exit != 0 || (step.Status != "executed" && !(step.Name == "tests" && step.Status == "reused"))
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

    internal static TestExecutionRecord ValidateTests(string root, IEnumerable<string>? requiredProjects = null, TestEnvironmentContext? context = null)
    {
        var record = Read<TestExecutionRecord>(root, TestsPath);
        var candidate = Candidate(root, out var snapshot);
        return ValidateTests(root, record, candidate, snapshot, requiredProjects, context: context);
    }

    private static TestExecutionRecord ValidateTests(string root, TestExecutionRecord record, string candidate,
        RepositorySnapshot snapshot, IEnumerable<string>? requiredProjects = null, CommonStageRecord? build = null, TestEnvironmentContext? context = null)
    {
        if (record.Version != 2 || record.Candidate != candidate || string.IsNullOrWhiteSpace(record.Round))
            throw new InvalidDataException("engineering evidence candidate identity mismatch or invalid version/round");
        ValidateMaterials(root, record.Materials);
        var expected = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot));
        if (expected.Length == 0 || !expected.SequenceEqual(record.Projects.Select(static result => result.Project)))
            throw new InvalidDataException("engineering evidence does not cover every current test project exactly once");
        TestInputManifest? plan = null;
        if (record.Materials.Any(material => material.Path == AffectedTestPlan.PathName))
        {
            build ??= ValidateBuild(root, candidate, record.Round);
            if (build.Round != record.Round) throw new InvalidDataException("tests belong to a different build round");
            if (!build.Materials.Any(material => material.Path == AffectedTestPlan.PathName)
                || !record.Materials.Any(material => material.Path == BuildPath)) throw new InvalidDataException("test plan is not bound to the current build");
            plan = Read<TestInputManifest>(root, AffectedTestPlan.PathName);
            AffectedTestPlan.Validate(plan);
            if (plan.Candidate != candidate) throw new InvalidDataException("test input manifest candidate mismatch");
        }
        var producer = AffectedTestPlan.ProducerIdentity();
        if (plan is not null)
        {
            context ??= CommonStages.TestEnvironment(root);
            AffectedEnvironmentObservation.Write(root, "downstream-validation", plan, record.Candidate, context: context);
        }
        var evidenceByDirectory = new Dictionary<string, TestResultEvidence>(StringComparer.Ordinal);
        TestResultEvidence LoadTrx(string file)
        {
            var directory = Path.GetDirectoryName(file)!;
            if (!evidenceByDirectory.TryGetValue(directory, out var evidence))
                evidenceByDirectory[directory] = evidence = TestResultEvidence.Load(directory);
            return evidence;
        }
        // Materials were validated above. Share those hashes and each parsed TRX
        // across all project actions covered by that file.
        var validatedHashes = record.Materials.ToDictionary(material => Path.Combine(root, material.Path), material => material.Sha256, StringComparer.Ordinal);
        foreach (var project in record.Projects)
        {
            if (project.Exit != 0 || project.Error is not null || project.Executed < 0
                || project.Executed + project.Coverage.Where(item => item.Status == "reused").Sum(item => item.Covered) <= 0)
                throw new InvalidDataException($"test project failed: {project.Project}: {project.Error}");
            if (plan is not null) ValidateCoverage(root, record, project, plan, LoadTrx, path => validatedHashes[path], context!, producer);
            else if (project.Coverage.Length != 0) throw new InvalidDataException("coverage has no current input manifest");
            if (project.Executed == 0) continue;
            if (!RepoPath.TryCreate(project.Results, out _)) throw new InvalidDataException("invalid TRX path");
            var directory = Path.Combine(root, project.Results);
            var files = Directory.GetFiles(directory, "*.trx").Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).ToArray();
            if (files.Length == 0 || files.Any(path => !record.Materials.Any(material => material.Path == path)))
                throw new InvalidDataException($"missing bound TRX material for {project.Project}");
            if (LoadTrx(Path.Combine(root, files[0])).Executed != project.Executed)
                throw new InvalidDataException($"TRX count mismatch: {project.Project}");
        }
        foreach (var project in requiredProjects ?? [])
            if (!record.Projects.Any(result => result.Project == project && result.Exit == 0 && result.Executed + result.Coverage.Where(item => item.Status == "reused").Sum(item => item.Covered) > 0))
                throw new InvalidDataException($"base test project has no successful candidate coverage: {project}");
        return record;
    }
    private static void ValidateCoverage(string root, TestExecutionRecord record, TestProjectExecution project, TestInputManifest plan, Func<string, TestResultEvidence> load, Func<string, string> hash, TestEnvironmentContext context, string producer)
    {
        var actions = plan.Actions.Where(action => action.Project == project.Project)
            .Select(action => AffectedTestPlan.BindEnvironment(action, context)).OrderBy(action => action.Scope, StringComparer.Ordinal).ToArray();
        if (actions.Length == 0 || !actions.Select(action => action.Scope).SequenceEqual(project.Coverage.Select(item => item.Scope)))
            throw new InvalidDataException("required test scopes are missing, duplicated, or out of order");
        var currentCount = 0;
        foreach (var (action, coverage) in actions.Zip(project.Coverage))
        {
            if (action.Identity != AffectedTestPlan.Identity(action) || action.Identity != coverage.Identity
                || action.Producer != producer || action.Environment != context.ForValues(action.UsesExplicitValues) || coverage.Covered < 0
                || string.IsNullOrWhiteSpace(coverage.Reason)) throw new InvalidDataException("test action input identity mismatch");
            if (coverage.Results.Any(path => !record.Materials.Any(material => material.Path == path)) || coverage.Results.Length == 0)
                throw new InvalidDataException("missing bound coverage TRX");
            if (coverage.Status == "reused")
            {
                if (!action.UsesExplicitValues) throw new InvalidDataException("unknown execution dependencies cannot be reused");
                AffectedTestCache.ValidateSource(action, coverage.Source, coverage.Results.Select(path => System.IO.Path.Combine(root, path)).ToArray(), load, hash: hash);
                if (coverage.Covered != coverage.Source.Covered) throw new InvalidDataException("reused count mismatch");
            }
            else if (coverage.Status == "executed")
            {
                if (coverage.Source.Candidate != record.Candidate || coverage.Source.Round != record.Round
                    || coverage.Source.ActionIdentity != action.Identity || coverage.Covered != coverage.Source.Covered)
                    throw new InvalidDataException("executed coverage has an old success source");
                if (action.UsesExplicitValues)
                    AffectedTestCache.ValidateSource(action, coverage.Source, coverage.Results.Select(path => System.IO.Path.Combine(root, path)).ToArray(), load, hash: hash);
                currentCount += coverage.Covered;
            }
            else throw new InvalidDataException("test scope is failed or uncovered");
        }
        if (currentCount != project.Executed) throw new InvalidDataException("executed test coverage exceeds TRX count");
    }

}
