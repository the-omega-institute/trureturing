using StrataLint.Engine;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.EngineeringScope;

internal static partial class CommonExecutionEvidence
{
    internal static IReadOnlyDictionary<string, RegisteredTestInput> TestInputs(string root, RepositorySnapshot snapshot)
    {
        var files = snapshot.Files.Values.Select(file => new EngineeringSource(file.Path.Value, file.Text)).ToArray();
        var registry = EngineeringProjectRegistry.Read(files);
        var sources = registry.Sources(files);
        var projects = registry.Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var paths = snapshot.Files.Keys.Select(path => path.Value).ToArray();
        var compile = new Dictionary<string, string>(StringComparer.Ordinal);
        var materials = new Dictionary<string, object>(StringComparer.Ordinal);
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
                value = name == "STRATALINT_TEST_ENVIRONMENT" ? ExecutionEnvironment(root) : Environment.GetEnvironmentVariable(name) is { Length: > 0 } value ? value
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
                        row.RootNamespace, row.NamespaceExclude, row.GlobalNamespaceExceptions,
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
            // Projects share one content/mode record per file in this snapshot.
            if (materials.TryGetValue(path, out var cached)) return cached;
            // Compile registrations must name concrete compile/options materials.
            if (path is EngineeringProjectRegistry.ManifestPath or "Meta/FILEMAP.toml")
                throw new InvalidDataException($"register relevant inputs directly, not the whole registration manifest: {path}");
            var file = snapshot.Files[RepoPath.CreateKnown(path)];
            var executable = !OperatingSystem.IsWindows() && (File.GetUnixFileMode(Path.Combine(root, path))
                & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0;
            var material = new { path, mode = executable ? "executable" : "regular", sha256 = Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())) };
            materials.Add(path, material);
            return material;
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
