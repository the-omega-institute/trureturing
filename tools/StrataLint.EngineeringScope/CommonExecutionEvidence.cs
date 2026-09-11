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
internal sealed record StageStep(string Name, int RawExit, int Exit, string Status, string Log,
    string? InputFingerprint = null, string? ExecutionCandidate = null, string? ExecutionRound = null);
internal sealed record CommonStageRecord(int Version, string Candidate, string Round, StageStep[] Steps, ExecutionMaterial[] Materials);
internal sealed record RegisteredCheckReport(string Producer, string Artifact, string[] Materials);
internal sealed record RegisteredCommonCheck(string Id, string[] ProgramProjects, string[] Materials,
    string[] MaterialExcludes, string[] PathInventory, RegisteredCheckReport[] ReportInputs);
internal sealed record CommonCheckManifest(string Schema, RegisteredCommonCheck[] Checks);

internal static class CommonExecutionEvidence
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
    internal static readonly string[] EngineeringSteps = ["restore-CompileFailProof", "restore-BannedApiCompileFailProof", "tests", "selftest-first", "selftest-second", "capability-proof", "banned-api-proof"];
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
        if (manifest.Schema != "ci-check-input-registration-v1" || manifest.Checks is null)
            throw new InvalidDataException("invalid common check registration schema");
        var expected = new[] { "SL-001", "SL-002", "SL-003", "SL-004", "SL-006", "SL-008", "SL-010", "SL-011", "SL-012", "SL-015", "SL-017", "SL-018", "SL-019", "SL-020", "SL-021", "SL-023", "SL-025", "SL-026", "selftest-pair", "capability-proof", "banned-api-proof", "scribe-projections", "scribe-describe", "scribe-markdown", "filemap" };
        if (!manifest.Checks.Select(check => check.Id).Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
            throw new InvalidDataException("common check registration must contain the complete current check set");
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
            foreach (var report in check.ReportInputs)
            {
                if (string.IsNullOrWhiteSpace(report.Producer) || string.IsNullOrWhiteSpace(report.Artifact)
                    || report.Materials is null || report.Materials.Length == 0)
                    throw new InvalidDataException($"invalid report input registration: {check.Id}");
                if (!snapshot.Files.ContainsKey(RepoPath.CreateKnown(report.Producer)))
                    throw new InvalidDataException($"check {check.Id} references missing producer: {report.Producer}");
                ValidatePatterns(report.Materials, [], check.Id);
                _ = EngineeringProjectRegistry.ExpandInputs(paths, report.Materials, [], check.Id);
            }
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

    // Computes identity from each check's declared projection. Unrelated registry rows and
    // candidate/round labels are deliberately excluded from this input fingerprint.
    internal static IReadOnlyDictionary<string, string> CheckInputFingerprints(string root,
        RepositorySnapshot snapshot)
    {
        var files = snapshot.Files.Values.Select(item => new EngineeringSource(item.Path.Value, item.Text)).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        var checks = ReadCheckManifest(snapshot, registry);
        var paths = snapshot.Files.Keys.Select(path => path.Value).ToArray();
        var projects = registry.Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var check in checks)
        {
            var materialPaths = EngineeringProjectRegistry.ExpandInputs(paths, check.Materials, check.MaterialExcludes, check.Id)
                .Concat(EngineeringProjectRegistry.ExpandInputs(paths, check.PathInventory, [], check.Id));
            foreach (var report in check.ReportInputs)
                materialPaths = materialPaths.Concat(EngineeringProjectRegistry.ExpandInputs(paths, report.Materials, [], check.Id));
            var addressedProjects = check.ProgramProjects.Order(StringComparer.Ordinal).Select(path =>
                projects.TryGetValue(path, out var project)
                    ? new { project.Path, project.Assembly, project.Role, project.References, project.Include, project.Exclude }
                    : throw new InvalidDataException($"check {check.Id} references unregistered project: {path}"));
            var entries = materialPaths.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).Select(path =>
            {
                var item = snapshot.Files[RepoPath.CreateKnown(path)];
                return new { path, sha256 = Convert.ToHexStringLower(SHA256.HashData(item.RawBytes.AsSpan())) };
            });
            result.Add(check.Id, Digest(new { check.Id, projects = addressedProjects, materials = entries,
                reports = check.ReportInputs.OrderBy(item => item.Producer, StringComparer.Ordinal) }));
        }
        return result;
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
        if (candidate != Candidate(root)) throw new InvalidDataException("candidate changed during build");
        var round = Guid.NewGuid().ToString("N");
        var record = new CommonStageRecord(2, candidate, round, BindStepIdentity(steps, candidate, round),
            Materials(root, binaries.Concat(steps.Select(step => step.Log))));
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
        var record = new CommonStageRecord(2, candidate, build.Round, BindStepIdentity(steps, candidate, build.Round),
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

    internal static void SealCurrent(string root, CommonStageRecord build, StageStep[] steps,
        IReadOnlyDictionary<string, string>? inputFingerprints = null)
    {
        var candidate = Candidate(root, out var snapshot);
        ValidateStartedBuild(root, build, candidate);
        RequirePassed(steps, CurrentSteps);
        _ = RawLeanReportArtifact.ReadFile(Path.Combine(root, ReportPath), snapshot, validateMaterials: true);
        var currentMaterials = ReportPaths.Append(BuildPath)
            .Concat(File.Exists(Path.Combine(root, CheckManifestPath)) ? [CheckManifestPath] : [])
            .Concat(File.Exists(Path.Combine(root, ScribeMarkdownPaths)) ? [ScribeMarkdownPaths] : [])
            .Concat(steps.Select(step => step.Log));
        var record = new CommonStageRecord(2, build.Candidate, build.Round, BindStepIdentity(steps, build.Candidate, build.Round, inputFingerprints),
            Materials(root, currentMaterials));
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
        _ = ReadCheckManifest(snapshot);
        if (!record.Materials.Any(material => material.Path == CheckManifestPath))
            throw new InvalidDataException("current has no bound common check registration");
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
        if (record.Version is not (1 or 2) || record.Candidate != candidate || record.Round != round)
            throw new InvalidDataException("common evidence candidate identity or round mismatch");
        RequirePassed(record.Steps);
        ValidateMaterials(root, record.Materials);
    }

    private static StageStep[] BindStepIdentity(IEnumerable<StageStep> steps, string candidate, string round,
        IReadOnlyDictionary<string, string>? inputFingerprints = null) =>
        steps.Select(step => step.Status == "reused"
            ? step
            : step with { InputFingerprint = inputFingerprints is not null && inputFingerprints.TryGetValue(step.Name, out var fingerprint)
                    ? fingerprint : step.InputFingerprint,
                ExecutionCandidate = candidate, ExecutionRound = round }).ToArray();

    private static void RequirePassed(IEnumerable<StageStep> steps, string[]? required = null)
    {
        if (steps.Any(step => step.Exit != 0 || step.Status is not ("executed" or "reused")
                || step.RawExit != (step.Name is "capability-proof" or "banned-api-proof" ? 1 : 0)
                || step.Status == "reused" && (!ValidCandidate(step.ExecutionCandidate)
                    || !ValidRound(step.ExecutionRound) || string.IsNullOrWhiteSpace(step.InputFingerprint))))
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

    internal static IReadOnlyDictionary<string, RegisteredTestInput> TestInputs(string root, RepositorySnapshot snapshot)
    {
        var files = snapshot.Files.Values.Select(file => new EngineeringSource(file.Path.Value, file.Text)).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        var sources = registry.Sources(files);
        var projects = registry.Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var paths = snapshot.Files.Keys.Select(path => path.Value).ToArray();
        var compile = new Dictionary<string, string>(StringComparer.Ordinal);
        // Validate ALL current declarations before selection, including disabled tests.
        var buildInputs = projects.Values.ToDictionary(project => project.Path, project =>
            EngineeringProjectRegistry.ExpandInputs(paths, project.BuildInputs!, [], project.Path), StringComparer.Ordinal);
        var executionInputs = projects.Values.Where(project => project.IsTest).ToDictionary(project => project.Path, project =>
            EngineeringProjectRegistry.ExpandInputs(paths, project.ExecutionInputs!, project.ExecutionExcludes!, project.Path), StringComparer.Ordinal);
        var result = new Dictionary<string, RegisteredTestInput>(StringComparer.Ordinal);
        foreach (var project in projects.Values.Where(project => project.Ci))
        {
            var environment = project.ExecutionEnvironment!.Order(StringComparer.Ordinal).Select(name => new
            {
                name,
                value = Environment.GetEnvironmentVariable(name) is { Length: > 0 } value ? value
                    : throw new InvalidDataException($"missing declared execution environment: {project.Path}: {name}"),
            }).ToArray();
            var relevant = new HashSet<string>(executionInputs[project.Path], StringComparer.Ordinal);
            AddCompilePaths(project.Path, relevant);
            var fingerprint = Digest(new
            {
                contract = TestContract, compile = Compile(project.Path),
                inputs = project.ExecutionInputs!.Order(StringComparer.Ordinal),
                excludes = project.ExecutionExcludes!.Order(StringComparer.Ordinal),
                project.Role, project.Ci, project.Owner, project.OwnedTestAssembly, project.TestPartition,
                materials = executionInputs[project.Path].Select(path => ExecutionMaterial(path, relevant)), environment,
            });
            result.Add(project.Path, new(project.Path, project.Assembly, fingerprint));
        }
        if (result.Count == 0) throw new InvalidDataException("candidate contains zero registered CI test projects");
        return result;

        string Compile(string path)
        {
            if (compile.TryGetValue(path, out var cached)) return cached;
            var project = projects[path];
            var value = Digest(new
            {
                contract = "registered-compile-v1", project.Path, project.Assembly,
                include = project.Include.Order(StringComparer.Ordinal), exclude = project.Exclude.Order(StringComparer.Ordinal),
                build_inputs = project.BuildInputs!.Order(StringComparer.Ordinal),
                references = project.References.Order(StringComparer.Ordinal).Select(reference => new { path = reference, input = Compile(reference) }),
                materials = sources[path].Select(source => source.Path).Concat(buildInputs[path]).Append(path)
                    .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).Select(Material),
            });
            compile.Add(path, value);
            return value;
        }

        void AddCompilePaths(string path, HashSet<string> relevant)
        {
            relevant.Add(path);
            relevant.UnionWith(sources[path].Select(source => source.Path));
            relevant.UnionWith(buildInputs[path]);
            foreach (var reference in projects[path].References) AddCompilePaths(reference, relevant);
        }

        object ExecutionMaterial(string path, HashSet<string> relevant)
        {
            // Runtime readers of registration data bind only rows addressed by their
            // declared material/compile closure, never unrelated manifest bytes.
            if (path == EngineeringProjectRegistry.ManifestPath)
                return new { path, projects = projects.Values.Where(row => relevant.Contains(row.Path))
                    .OrderBy(row => row.Path, StringComparer.Ordinal).Select(row => new
                    {
                        row.Path, row.Assembly, row.Role, row.Ci, row.Owner, row.OwnedTestAssembly, row.TestPartition,
                        include = row.Include.Order(StringComparer.Ordinal), exclude = row.Exclude.Order(StringComparer.Ordinal),
                        references = row.References.Order(StringComparer.Ordinal), build_inputs = row.BuildInputs!.Order(StringComparer.Ordinal),
                        execution_inputs = row.ExecutionInputs?.Order(StringComparer.Ordinal),
                        execution_excludes = row.ExecutionExcludes?.Order(StringComparer.Ordinal),
                        execution_environment = row.ExecutionEnvironment?.Order(StringComparer.Ordinal),
                    }) };
            if (path == "Meta/FILEMAP.toml")
            {
                var map = TomlSerializer.Deserialize<TomlTable>(snapshot.Files[RepoPath.CreateKnown(path)].Text)
                    ?? throw new InvalidDataException("invalid registered FILEMAP input");
                var rows = map.TryGetValue("files", out var value) && value is IEnumerable<object> entries
                    ? entries.Cast<TomlTable>().ToArray() : throw new InvalidDataException("registered FILEMAP input has no files array");
                var selected = rows.Where(row => row.TryGetValue("pattern", out var pattern) && pattern is string text
                    ? relevant.Any(FileMapGlob.CreateForAdmissionPlane(text).IsMatch)
                    : throw new InvalidDataException("registered FILEMAP row has no pattern"));
                return new { path, policy = map.Where(pair => pair.Key != "files").OrderBy(pair => pair.Key, StringComparer.Ordinal),
                    rows = selected.OrderBy(row => (string)row["pattern"], StringComparer.Ordinal)
                        .Select(row => row.OrderBy(pair => pair.Key, StringComparer.Ordinal).ToArray()) };
            }
            return Material(path);
        }

        object Material(string path)
        {
            // Compile registrations must name concrete compile/options materials.
            if (path is EngineeringProjectRegistry.ManifestPath or "Meta/FILEMAP.toml")
                throw new InvalidDataException($"register relevant inputs directly, not the whole registration manifest: {path}");
            var file = snapshot.Files[RepoPath.CreateKnown(path)];
            var executable = !OperatingSystem.IsWindows() && (File.GetUnixFileMode(Path.Combine(root, path))
                & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0;
            return new { path, mode = executable ? "executable" : "regular", sha256 = Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())) };
        }
    }

    private static string Digest<T>(T value) => Convert.ToHexStringLower(SHA256.HashData(JsonSerializer.SerializeToUtf8Bytes(value, JsonOptions)));

    internal static Dictionary<string, string> ValidateTestBuild(string root, CommonStageRecord build,
        IReadOnlyDictionary<string, RegisteredTestInput> inputs)
    {
        var assemblies = CommonBuildOutputs.TestAssemblies(root, build);
        if (!assemblies.Keys.Order(StringComparer.Ordinal).SequenceEqual(inputs.Keys.Order(StringComparer.Ordinal)))
            throw new InvalidDataException("build test inventory disagrees with current CI registration");
        foreach (var (project, path) in assemblies)
            if (!RepoPath.TryCreate(path, out _) || Path.GetFileNameWithoutExtension(path) != inputs[project].Assembly)
                throw new InvalidDataException($"build test assembly disagrees with registration: {project}: {path}");
        return assemblies;
    }

    internal static TestExecutionRecord ValidateTests(string root, IEnumerable<string>? requiredProjects = null)
    {
        var candidate = Candidate(root, out var snapshot);
        var build = ValidateBuild(root, candidate, null);
        var tests = ValidateTests(root, Read<TestExecutionRecord>(root, TestsPath), candidate, snapshot, requiredProjects);
        if (tests.Round != build.Round) throw new InvalidDataException("tests belong to a different build round");
        return tests;
    }

    private static TestExecutionRecord ValidateTests(string root, TestExecutionRecord record, string candidate,
        RepositorySnapshot snapshot, IEnumerable<string>? requiredProjects = null)
    {
        if (record.Version != 2 || record.Candidate != candidate || !ValidRound(record.Round)
            || record.Projects is null || record.Materials is null)
            throw new InvalidDataException("engineering evidence candidate identity mismatch or invalid version/round");
        var inputs = TestInputs(root, snapshot);
        _ = ValidateTestBuild(root, Read<CommonStageRecord>(root, BuildPath), inputs);
        if (!inputs.Keys.Order(StringComparer.Ordinal).SequenceEqual(record.Projects.Select(result => result.Project)))
            throw new InvalidDataException("engineering evidence does not cover every current test project exactly once");
        var bound = new List<string>();
        foreach (var project in record.Projects)
            bound.AddRange(ValidateProject(root, record, project, inputs[project.Project]).Select(material => material.Path));
        if (!bound.Order(StringComparer.Ordinal).SequenceEqual(record.Materials.Select(material => material.Path).Order(StringComparer.Ordinal)))
            throw new InvalidDataException("engineering evidence contains unowned or duplicate TRX material");
        foreach (var project in requiredProjects ?? [])
            if (!inputs.ContainsKey(project))
                throw new InvalidDataException($"base test project has no current accepted-success coverage: {project}");
        return record;
    }

    private static bool ValidRound(string? round) => !string.IsNullOrWhiteSpace(round)
        && round.All(character => char.IsAsciiLetterOrDigit(character) || character == '-');
    private static bool ValidCandidate(string? candidate) => candidate?.Length == 64 && candidate.All(char.IsAsciiHexDigit);

    private static ExecutionMaterial[] ValidateProject(string root, TestExecutionRecord record, TestProjectExecution project, RegisteredTestInput input)
    {
        if (project.Project != input.Project || project.InputFingerprint != input.Fingerprint)
            throw new InvalidDataException($"test input identity mismatch: {project.Project}");
        if (project.Status is not ("executed" or "reused") || !ValidCandidate(project.ExecutionCandidate) || !ValidRound(project.ExecutionRound)
            || project.Status == "executed" && (project.ExecutionCandidate != record.Candidate || project.ExecutionRound != record.Round))
            throw new InvalidDataException($"invalid original execution provenance: {project.Project}");
        if (project.Exit != 0 || project.Error is not null || project.Executed <= 0)
            throw new InvalidDataException($"test project failed: {project.Project}: {project.Error}");
        var prefix = $"{RootPath}/trx/{project.ExecutionCandidate}/{project.ExecutionRound}/{project.InputFingerprint}/";
        if (!RepoPath.TryCreate(project.Results, out _) || !project.Results.StartsWith(prefix, StringComparison.Ordinal))
            throw new InvalidDataException($"TRX path disagrees with original execution identity: {project.Project}");
        var directory = Path.Combine(root, project.Results);
        var actual = Directory.GetFiles(directory, "*.trx").Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            .Order(StringComparer.Ordinal).ToArray();
        var materials = record.Materials.Where(material => material.Path.StartsWith(project.Results + "/", StringComparison.Ordinal))
            .OrderBy(material => material.Path, StringComparer.Ordinal).ToArray();
        if (actual.Length == 0 || !actual.SequenceEqual(materials.Select(material => material.Path)))
            throw new InvalidDataException($"missing or extra bound TRX material: {project.Project}");
        ValidateMaterials(root, materials);
        var evidence = TestResultEvidence.Load(directory);
        if (evidence.Executed != project.Executed) throw new InvalidDataException($"TRX count mismatch: {project.Project}");
        if (evidence.CountAssembly(input.Assembly) == 0 || evidence.ExecutedTests.Any(test =>
                !StringComparer.OrdinalIgnoreCase.Equals(test.Assembly, input.Assembly)))
            throw new InvalidDataException($"TRX assembly identity mismatch: {project.Project}: {input.Assembly}");
        return materials;
    }

    // Optional seeds contain tests.json plus the original material paths relative to this
    // directory. Import is per project: a damaged row cannot discard another valid row.
    internal static Dictionary<string, TestProjectExecution> ImportTestSeed(string root,
        IReadOnlyDictionary<string, RegisteredTestInput> inputs, TextWriter output)
    {
        var accepted = new Dictionary<string, TestProjectExecution>(StringComparer.Ordinal);
        var seedRoot = Path.Combine(root, TestSeedPath);
        TestExecutionRecord seed;
        JsonElement[] seedProjects;
        try
        {
            var document = Read<JsonElement>(seedRoot, "tests.json");
            if (!document.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal)
                .SequenceEqual(new[] { "candidate", "materials", "projects", "round", "version" }))
                throw new InvalidDataException("invalid test seed envelope fields");
            seedProjects = document.GetProperty("projects").EnumerateArray().ToArray();
            // Decode optional rows independently. Bad material loses its own TRX binding;
            // the same project validator then rejects only the affected project.
            var materials = new List<ExecutionMaterial>();
            foreach (var row in document.GetProperty("materials").EnumerateArray())
            {
                try
                {
                    if (row.Deserialize<ExecutionMaterial>(JsonOptions) is { Path: not null, Sha256: not null } material)
                        materials.Add(material);
                }
                catch (JsonException) { }
            }
            seed = new(document.GetProperty("version").GetInt32(), document.GetProperty("candidate").GetString()!,
                document.GetProperty("round").GetString()!, [], materials.ToArray());
            if (seed.Version != 2 || !ValidCandidate(seed.Candidate) || !ValidRound(seed.Round) || seed.Projects is null || seed.Materials is null)
                throw new InvalidDataException("unsupported test seed schema/identity");
        }
        catch (Exception exception)
        {
            output.WriteLine($"ENGINEERING_TEST_SEED_UNAVAILABLE reason={JsonSerializer.Serialize(exception.Message)}");
            return accepted;
        }
        foreach (var input in inputs.Values)
        {
            try
            {
                var row = seedProjects.Single(row => row.ValueKind == JsonValueKind.Object
                    && row.TryGetProperty("project", out var path) && path.ValueKind == JsonValueKind.String && path.GetString() == input.Project);
                var project = row.Deserialize<TestProjectExecution>(JsonOptions)
                    ?? throw new InvalidDataException("missing seed project row");
                var materials = ValidateProject(seedRoot, seed, project, input);
                foreach (var material in materials)
                {
                    var destination = Path.Combine(root, material.Path);
                    Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                    File.Copy(Path.Combine(seedRoot, material.Path), destination, overwrite: true);
                }
                // Recheck the copied materials, using the same validator as every consumer.
                _ = ValidateProject(root, seed, project, input);
                accepted.Add(project.Project, project with { Status = "reused" });
            }
            catch (Exception exception)
            {
                output.WriteLine($"ENGINEERING_TEST_SEED_MISS project={JsonSerializer.Serialize(input.Project)} reason={JsonSerializer.Serialize(exception.Message)}");
            }
        }
        return accepted;
    }

    // This must only be called after engineering acceptance. Transport/save is optional;
    // acceptance errors are not swallowed as cache misses or save failures.
    internal static bool ExportTestSeed(string root, TextWriter output, string? destination = null)
    {
        _ = ValidateEngineering(root);
        var tests = ValidateTests(root);
        destination ??= Path.Combine(root, TestSeedPath);
        var staging = destination + ".tmp-" + Guid.NewGuid().ToString("N");
        try
        {
            Directory.CreateDirectory(staging);
            foreach (var material in tests.Materials)
            {
                var target = Path.Combine(staging, material.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Path.Combine(root, material.Path), target);
            }
            Write(staging, "tests.json", tests);
            ValidateMaterials(staging, tests.Materials);
            if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true);
            Directory.Move(staging, destination);
            output.WriteLine("ENGINEERING_TEST_SEED_SAVED");
            return true;
        }
        catch (Exception exception)
        {
            output.WriteLine($"ENGINEERING_TEST_SEED_NOT_SAVED reason={JsonSerializer.Serialize(exception.Message)}");
            return false;
        }
        finally
        {
            try { if (Directory.Exists(staging)) Directory.Delete(staging, recursive: true); }
            catch (IOException) { } // Optional seed cleanup cannot change a test result.
            catch (UnauthorizedAccessException) { }
        }
    }
}
