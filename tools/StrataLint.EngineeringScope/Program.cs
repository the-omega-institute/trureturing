using System.Diagnostics;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    public static int Main(string[] arguments) => Run(arguments, TestResultEvidence.Load, Console.Out, Console.Error);

    internal static int Run(IReadOnlyList<string> arguments, Func<string, TestResultEvidence> evidenceLoader, TextWriter output, TextWriter error)
    {
        try
        {
            if (arguments.FirstOrDefault() == "lean-utility-input")
            {
                var result = LeanUtilityInputCommand.Run(
                    () => GitRepositorySnapshotReader.ReadCurrent(Directory.GetCurrentDirectory()), arguments.Skip(1).ToArray());
                output.Write(result.Output);
                error.Write(result.Error);
                return result.ExitCode;
            }
            if (arguments.FirstOrDefault() == "lean-cache-writer")
            {
                var result = LeanCacheEnsureCommand.RunWithWriter(Directory.GetCurrentDirectory(),
                    arguments.Skip(1).ToArray(), new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());
                output.Write(result.Output);
                error.Write(result.Error);
                return result.ExitCode ?? (result.Success ? 0 : 2);
            }
            if (arguments.FirstOrDefault() == "truth-release-select")
                return TruthReleaseSelection.Run(arguments, output);
            if (arguments.FirstOrDefault() is "transport-pack" or "transport-verify")
                return CiTransport.Run(arguments, output);
            if (arguments.FirstOrDefault() is "build" or "engineering" or "current" or "delta")
            {
                if (arguments.Count is not (3 or 5) || arguments[1] != "--repository"
                    || arguments.Count == 5 && !(arguments[0] == "delta" && arguments[3] == "--base"
                        || arguments[0] == "engineering" && arguments[3] == "--build-round"))
                    throw new ArgumentException("stage --repository ROOT [--base SHA | --build-round ROUND]");
                return new CommonStages(Path.GetFullPath(arguments[2]), output).Run(arguments[0], arguments.Count == 5 && arguments[3] == "--base" ? arguments[4] : null,
                    arguments.Count == 5 && arguments[3] == "--build-round" ? arguments[4] : null);
            }
            if (arguments.FirstOrDefault() == "verify-trx")
            {
                try { return VerifyTrx(arguments.Skip(1).ToArray(), evidenceLoader, output); }
                catch (Exception exception) { error.WriteLine($"TEST_EVIDENCE_FAILED {exception.Message}"); return 2; }
            }
            if (arguments.FirstOrDefault() == "list-test-owner-assemblies")
            {
                var root = RepositoryOption(arguments.Skip(1).ToArray());
                var assemblies = RepositoryRules.CalculateOwnerAssemblies(RepositoryRules.ReadTrackedProjects(root));
                if (assemblies.Length == 0) throw new InvalidDataException("list-test-owner-assemblies derived zero owner assemblies");
                foreach (var assembly in assemblies) output.WriteLine(assembly);
                return 0;
            }
            string? buildRound = null;
            if (arguments.Count == 5 && arguments[3] == "--build-round")
            {
                buildRound = arguments[4];
                arguments = arguments.Take(3).ToArray();
            }
            var repository = RepositoryOption(arguments, allowAll: true);
            var build = buildRound is null ? null : CommonExecutionEvidence.ValidateBuild(repository, buildRound);
            var testAssemblies = build is null ? null : CommonBuildOutputs.TestAssemblies(repository, build);
            return RunCurrentTests(repository, (project, results) => RunTests(repository,
                testAssemblies is null ? project : testAssemblies[project], results), output, build);
        }
        catch (Exception exception)
        {
            error.WriteLine($"ENGINEERING_TEST_PLAN_FAILED {exception.Message}");
            return 2;
        }
    }

    private static string RepositoryOption(IReadOnlyList<string> arguments, bool allowAll = false)
    {
        if (allowAll && arguments.Count == 3 && arguments.Count(static argument => argument == "--all") == 1)
            arguments = arguments.Where(static argument => argument != "--all").ToArray();
        return arguments.Count == 2 && arguments[0] == "--repository" && !string.IsNullOrWhiteSpace(arguments[1])
            ? Path.GetFullPath(arguments[1])
            : throw new ArgumentException("options must be exactly --repository value");
    }

    internal static int RunCurrentTests(string root, Func<string, string, int> run, TextWriter output, CommonStageRecord? build = null)
    {
        var candidate = CommonExecutionEvidence.Candidate(root);
        var projects = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(CommonExecutionEvidence.Snapshot(root)));
        if (projects.Length == 0) throw new InvalidDataException("candidate contains zero test projects");
        var round = build?.Round ?? Guid.NewGuid().ToString("N");
        var invocation = Guid.NewGuid().ToString("N");
        var records = new List<TestProjectExecution>();
        output.WriteLine($"ENGINEERING_TEST_PLAN state=full selected={projects.Length} candidate={candidate}");
        foreach (var project in projects)
        {
            output.WriteLine($"ENGINEERING_TEST_PROJECT project={JsonSerializer.Serialize(project)}");
            var relative = $"{CommonExecutionEvidence.RootPath}/trx/{invocation}/{records.Count}";
            var directory = Path.Combine(root, relative);
            Directory.CreateDirectory(directory);
            var exit = 2;
            var executed = 0;
            string? failure = null;
            try
            {
                exit = run(project, directory);
                var evidence = TestResultEvidence.Load(directory);
                executed = evidence.Executed;
                if (exit != 0) failure = $"dotnet test exit={exit}";
            }
            catch (Exception exception) { failure = exception.Message; }
            records.Add(new(project, relative, exit, executed, failure));
            output.WriteLine($"ENGINEERING_TEST_EXECUTED project={JsonSerializer.Serialize(project)} raw_exit={exit} executed={executed} error={JsonSerializer.Serialize(failure)}");
        }
        var paths = records.SelectMany(record => Directory.GetFiles(Path.Combine(root, record.Results), "*.trx"))
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'));
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.TestsPath,
            new TestExecutionRecord(1, candidate, round, records.ToArray(), CommonExecutionEvidence.Materials(root, paths)));
        if (CommonExecutionEvidence.Candidate(root) != candidate) throw new InvalidDataException("candidate changed during test execution");
        return records.Any(static record => record.Exit != 0 || record.Error is not null || record.Executed == 0) ? 1 : 0;
    }

    private static int RunTests(string root, string project, string results)
    {
        var start = new ProcessStartInfo("dotnet") { WorkingDirectory = root, UseShellExecute = false };
        start.Environment["DOTNET_CLI_UI_LANGUAGE"] = "en-US";
        if (Directory.Exists(Path.Combine(root, CommonBuildOutputs.PackagesPath)))
            start.Environment["NUGET_PACKAGES"] = Path.Combine(root, CommonBuildOutputs.PackagesPath);
        foreach (var argument in BuildTestArguments(project, results)) start.ArgumentList.Add(argument);
        using var process = Process.Start(start) ?? throw new InvalidOperationException("could not start dotnet test");
        process.WaitForExit();
        return process.ExitCode;
    }

    internal static IReadOnlyList<string> BuildTestArguments(string projectPath, string resultsDirectory) =>
        new[] { "test", projectPath, "--configuration", "Release", "--verbosity", "minimal", "--no-restore", "--no-build" }
            .Concat(["--logger", "trx;LogFilePrefix=engineering", "--results-directory", resultsDirectory]).ToArray();

    private static int VerifyTrx(IReadOnlyList<string> arguments, Func<string, TestResultEvidence> load, TextWriter output)
    {
        string? directory = null;
        var required = new List<string>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw new ArgumentException("verify-trx options must be --name value pairs");
            switch (arguments[index])
            {
                case "--results-directory" when directory is null: directory = arguments[index + 1]; break;
                case "--required-assembly" when !string.IsNullOrWhiteSpace(arguments[index + 1]): required.Add(arguments[index + 1]); break;
                default: throw new ArgumentException($"unknown verify-trx option: {arguments[index]}");
            }
        }
        if (string.IsNullOrWhiteSpace(directory)) throw new ArgumentException("--results-directory is required");
        var evidence = load(Path.GetFullPath(directory));
        foreach (var assembly in required)
        {
            var count = evidence.CountAssembly(assembly);
            if (count == 0) throw new InvalidDataException($"TRX has no executed identity from required assembly {assembly}");
            output.WriteLine($"ENGINEERING_BASE_FLOOR_EXECUTED assembly={assembly} evidence=trx executed={count}");
        }
        if (required.Count == 0) output.WriteLine($"TEST_EVIDENCE_ACCEPTED evidence=trx executed={evidence.Executed}");
        return 0;
    }
}
