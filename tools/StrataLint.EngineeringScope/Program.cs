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
            if (arguments.FirstOrDefault() is "check-seed-export" or "check-seed-import")
                return CommonExecutionEvidence.CheckSeedCommand(arguments, output);
            if (arguments.FirstOrDefault() == "truth-release-select")
                return TruthReleaseSelection.Run(arguments, output);
            if (arguments.FirstOrDefault() is "transport-pack" or "transport-verify")
                return CiTransport.Run(arguments, output);
            if (arguments.FirstOrDefault() is "build" or "engineering" or "current" or "delta")
            {
                if (arguments.Count < 3 || arguments[1] != "--repository")
                    throw new ArgumentException("stage --repository ROOT [--base SHA | --build-round ROUND] [--plan FILE --changes FILE]");
                string? baseSha = null, stageBuildRound = null, plan = null, changes = null;
                for (var i = 3; i < arguments.Count; i += 2)
                {
                    if (i + 1 >= arguments.Count) throw new ArgumentException("stage options must be name/value pairs");
                    switch (arguments[i])
                    {
                        case "--base" when arguments[0] == "delta" && baseSha is null: baseSha = arguments[i + 1]; break;
                        case "--build-round" when arguments[0] == "engineering" && stageBuildRound is null: stageBuildRound = arguments[i + 1]; break;
                        case "--plan" when plan is null: plan = arguments[i + 1]; break;
                        case "--changes" when changes is null: changes = arguments[i + 1]; break;
                        default: throw new ArgumentException("invalid stage option: " + arguments[i]);
                    }
                }
                return new CommonStages(Path.GetFullPath(arguments[2]), output).Run(arguments[0], baseSha, stageBuildRound, plan, changes);
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
            if (arguments.Count == 4 && arguments[2] == "--build-round")
            {
                buildRound = arguments[3];
                arguments = arguments.Take(2).ToArray();
            }
            var repository = RepositoryOption(arguments);
            var build = CommonExecutionEvidence.ValidateBuild(repository, buildRound);
            var inputs = CommonExecutionEvidence.TestInputs(repository, CommonExecutionEvidence.Snapshot(repository));
            var testAssemblies = CommonExecutionEvidence.ValidateTestBuild(repository, build, inputs);
            return RunCurrentTests(repository, (project, results) => RunTests(repository, testAssemblies[project], results), output, build);
        }
        catch (Exception exception)
        {
            error.WriteLine($"ENGINEERING_TEST_PLAN_FAILED {exception.Message}");
            return 2;
        }
    }

    private static string RepositoryOption(IReadOnlyList<string> arguments)
    {
        return arguments.Count == 2 && arguments[0] == "--repository" && !string.IsNullOrWhiteSpace(arguments[1])
            ? Path.GetFullPath(arguments[1])
            : throw new ArgumentException("options must be exactly --repository value");
    }

    internal static int RunCurrentTests(string root, Func<string, string, int> run, TextWriter output, CommonStageRecord? build = null)
    {
        var candidate = CommonExecutionEvidence.Candidate(root);
        var inputs = CommonExecutionEvidence.TestInputs(root, CommonExecutionEvidence.Snapshot(root));
        build ??= CommonExecutionEvidence.ValidateBuild(root);
        CommonExecutionEvidence.ValidateStartedBuild(root, build, candidate);
        _ = CommonExecutionEvidence.ValidateTestBuild(root, build, inputs);
        File.Delete(Path.Combine(root, CommonExecutionEvidence.TestsPath));
        var reused = CommonExecutionEvidence.ImportTestSeed(root, inputs, output);
        var projects = inputs.Keys.Order(StringComparer.Ordinal).ToArray();
        var invocation = Guid.NewGuid().ToString("N");
        var records = new List<TestProjectExecution>();
        output.WriteLine($"ENGINEERING_TEST_PLAN state=registered selected={projects.Length - reused.Count} reused={reused.Count} candidate={candidate}");
        foreach (var project in projects)
        {
            if (reused.TryGetValue(project, out var prior))
            {
                records.Add(prior);
                output.WriteLine($"ENGINEERING_TEST_REUSED project={JsonSerializer.Serialize(project)} origin_candidate={prior.ExecutionCandidate} origin_round={prior.ExecutionRound}");
                continue;
            }
            output.WriteLine($"ENGINEERING_TEST_PROJECT project={JsonSerializer.Serialize(project)}");
            var relative = $"{CommonExecutionEvidence.RootPath}/trx/{candidate}/{build.Round}/{inputs[project].Fingerprint}/{invocation}/{records.Count}";
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
            records.Add(new(project, inputs[project].Fingerprint, "executed", candidate, build.Round, relative, exit, executed, failure));
            output.WriteLine($"ENGINEERING_TEST_EXECUTED project={JsonSerializer.Serialize(project)} raw_exit={exit} executed={executed} error={JsonSerializer.Serialize(failure)}");
        }
        var paths = records.SelectMany(record => Directory.GetFiles(Path.Combine(root, record.Results), "*.trx"))
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'));
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.TestsPath,
            new TestExecutionRecord(2, candidate, build.Round, records.ToArray(), CommonExecutionEvidence.Materials(root, paths)));
        if (CommonExecutionEvidence.Candidate(root) != candidate) throw new InvalidDataException("candidate changed during test execution");
        CommonExecutionEvidence.ValidateStartedBuild(root, build, candidate);
        try { CommonExecutionEvidence.ValidateTests(root); }
        catch (Exception exception)
        {
            output.WriteLine($"ENGINEERING_TEST_EVIDENCE_FAILED {exception.Message}");
            return 1;
        }
        return 0;
    }

    private static int RunTests(string root, string project, string results)
    {
        var start = new ProcessStartInfo("dotnet") { WorkingDirectory = root, UseShellExecute = false };
        start.Environment["DOTNET_CLI_UI_LANGUAGE"] = "en-US";
        start.Environment["CI"] = "true";
        // The engineering runner executes repository tests, including tests
        // that create synthetic repositories.  A reusable workflow's fixed
        // candidate input belongs to the outer stage process; propagating it
        // into those synthetic fixtures makes their checkout commits fail the
        // outer identity check.  Tests that exercise this input set it
        // explicitly in their child environment.
        start.Environment.Remove("CI_WORKFLOW_CANDIDATE_SHA");
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
            output.WriteLine($"TEST_ASSEMBLY_EVIDENCE_ACCEPTED assembly={assembly} evidence=trx executed={count}");
        }
        if (required.Count == 0) output.WriteLine($"TEST_EVIDENCE_ACCEPTED evidence=trx executed={evidence.Executed}");
        return 0;
    }
}
