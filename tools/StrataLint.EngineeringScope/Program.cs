using System.Diagnostics;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    public static int Main(string[] arguments) =>
        Run(arguments, TestResultEvidence.Load, Console.Out, Console.Error);

    internal static int Run(
        IReadOnlyList<string> arguments,
        Func<string, TestResultEvidence> evidenceLoader,
        TextWriter standardOutput,
        TextWriter standardError)
    {
        try
        {
            if (arguments.FirstOrDefault() == "verify-trx")
            {
                try
                {
                    return VerifyTrx(
                        VerifyTrxOptions.Parse(arguments.Skip(1).ToArray()),
                        evidenceLoader,
                        standardOutput);
                }
                catch (Exception exception)
                {
                    standardError.WriteLine($"TEST_EVIDENCE_FAILED {exception.Message}");
                    return 2;
                }
            }

            if (arguments.FirstOrDefault() == "list-test-owner-assemblies")
            {
                return ListTestOwnerAssemblies(arguments.Skip(1).ToArray(), standardOutput);
            }

            var options = Options.Parse(arguments);
            return Execute(options, standardOutput);
        }
        catch (Exception exception)
        {
            standardError.WriteLine($"ENGINEERING_TEST_PLAN_FAILED {exception.Message}");
            return 2;
        }
    }

    private static int Execute(Options options, TextWriter output)
    {
        var head = GitText(options.RepositoryRoot, "rev-parse", "HEAD");
        if (!IsObjectId(options.Head, head.Length) || options.Head.All(character => character == '0'))
            throw new InvalidOperationException("deletion or invalid --head has no checked candidate tree");
        if (options.Head != head) throw new InvalidOperationException("--head must equal checkout HEAD");
        if (!IsObjectId(options.Before, head.Length))
            throw new InvalidOperationException("planning endpoint must be a complete fixed object ID");
        var initial = options.Before.All(character => character == '0');
        if (options.Event == "pull-request")
        {
            if (initial || options.Before != GitText(options.RepositoryRoot, "rev-parse", "HEAD^1"))
                throw new InvalidOperationException("PR --base must equal checked merge first parent");
            _ = GitText(options.RepositoryRoot, "rev-parse", "--verify", "HEAD^2");
            if (GitText(options.RepositoryRoot, "status", "--porcelain").Length != 0)
                throw new InvalidOperationException("PR planning requires a clean checked merge tree");
        }
        else if (!initial)
        {
            if (GitText(options.RepositoryRoot, "rev-parse", "--verify", options.Before + "^{commit}") != options.Before)
                throw new InvalidOperationException("push --before must name a complete commit object");
        }

        var manifest = EngineeringInputManifest.ReadCurrent(options.RepositoryRoot);
        var currentPaths = GitRawText(options.RepositoryRoot, "ls-files", "-z")
            .Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Where(path => File.Exists(Path.Combine(options.RepositoryRoot, path))).ToArray();
        var changedPaths = initial ? currentPaths : GitPaths(options.RepositoryRoot, options.Before, head);
        if (options.Event == "push")
            changedPaths = changedPaths.Concat(GitPaths(options.RepositoryRoot, head, null))
                .Concat(GitRawText(options.RepositoryRoot, "ls-files", "--others", "--exclude-standard", "-z")
                    .Split('\0', StringSplitOptions.RemoveEmptyEntries))
                .Distinct(StringComparer.Ordinal).ToArray();
        manifest.ValidateProjectCoverage(changedPaths.Where(path => File.Exists(Path.Combine(options.RepositoryRoot, path))));
        // Validate all selected material before classification or full routing.
        foreach (var path in changedPaths) _ = manifest.Owners(path);
        var admissionPlane = AdmissionPlanePolicy.Evaluate(
            File.ReadAllBytes(Path.Combine(options.RepositoryRoot, AdmissionPlanePolicy.FileMapPath)), changedPaths);
        if (!admissionPlane.IsAdmissible
            && !(options.Event == "push" && admissionPlane.Code == AdmissionPlanePolicy.MixedCode))
            throw new InvalidDataException($"{admissionPlane.Code} {admissionPlane.Path}: {admissionPlane.Message}");
        var full = options.Full || admissionPlane.Classification is AdmissionPlaneClassification.JudgeOnly or AdmissionPlaneClassification.Mixed;
        var plan = EngineeringTestPlanPolicy.EvaluateOrdinary(changedPaths, manifest, full);
        output.WriteLine($"ENGINEERING_INPUT_RANGE event={options.Event} mode={(initial ? "initial" : "endpoints")} before={options.Before} head={head}");
        WritePlan(plan, output);
        if (options.PlanOnly) return 0;
        return EngineeringTestExecutor.Execute(plan, invocation => RunTests(options.RepositoryRoot, invocation));
    }

    // Concurrent no-build tests keep their native behavior. Only a missing-output
    // build retry is serialized, because selected projects may share compiler outputs.
    private static readonly object BuildFallbackGate = new();

    private static int RunTests(
        string repositoryRoot,
        EngineeringTestInvocation invocation)
    {
        var resultsDirectory =
            Directory.CreateTempSubdirectory("stratalint-engineering-tests-").FullName;
        (int ExitCode, string StandardError) Run(bool noBuild)
        {
            var startInfo = new ProcessStartInfo
            {
                FileName = "dotnet",
                WorkingDirectory = repositoryRoot,
                RedirectStandardError = true,
                UseShellExecute = false,
            };
            startInfo.Environment["DOTNET_CLI_UI_LANGUAGE"] = "en-US";
            foreach (var argument in BuildTestArguments(
                invocation.ProjectPath,
                noBuild,
                resultsDirectory))
            {
                startInfo.ArgumentList.Add(argument);
            }

            using var process = Process.Start(startInfo)
                ?? throw new InvalidOperationException("could not start dotnet test");
            var standardError = process.StandardError.ReadToEndAsync();
            process.WaitForExit();
            return (process.ExitCode, standardError.GetAwaiter().GetResult());
        }

        try
        {
            var result = Run(noBuild: true);
            Console.Error.Write(result.StandardError);
            if ((result.ExitCode != 0 && ReportsMissingBuildOutput(result.StandardError))
                || (result.ExitCode == 0
                    && !Directory.EnumerateFiles(resultsDirectory, "*.trx").Any()))
            {
                Console.WriteLine(
                    $"ENGINEERING_TEST_RETRY project={JsonSerializer.Serialize(invocation.ProjectPath)} "
                    + "reason=missing-build-output");
                lock (BuildFallbackGate)
                {
                    result = Run(noBuild: false);
                }
                Console.Error.Write(result.StandardError);
            }
            if (result.ExitCode != 0) return result.ExitCode;

            try
            {
                var executed = TestResultEvidence.Load(resultsDirectory).Executed;
                Console.WriteLine(
                    $"ENGINEERING_TEST_EXECUTED project={JsonSerializer.Serialize(invocation.ProjectPath)} "
                    + $"evidence=trx executed={executed}");
                return 0;
            }
            catch (Exception exception)
            {
                Console.Error.WriteLine($"ENGINEERING_TEST_EVIDENCE_FAILED {exception.Message}");
                return 1;
            }
        }
        finally
        {
            Directory.Delete(resultsDirectory, recursive: true);
        }
    }

    internal static IReadOnlyList<string> BuildTestArguments(
        string projectPath,
        bool noBuild,
        string resultsDirectory)
    {
        var arguments = new List<string>
        {
            "test",
            projectPath,
            "--configuration",
            "Release",
            "--verbosity",
            "minimal",
        };
        if (noBuild) arguments.Add("--no-build");
        arguments.Add("--logger");
        arguments.Add("trx;LogFilePrefix=engineering");
        arguments.Add("--results-directory");
        arguments.Add(resultsDirectory);
        return arguments;
    }

    private static bool ReportsMissingBuildOutput(string output) =>
        output.ReplaceLineEndings("\n").Split('\n').Any(static line =>
            line.StartsWith("The argument ", StringComparison.Ordinal)
            && line.EndsWith(
                ".dll is invalid. Please use the /help option to check the list of valid arguments.",
                StringComparison.Ordinal));

    private static int ListTestOwnerAssemblies(
        IReadOnlyList<string> arguments,
        TextWriter standardOutput)
    {
        if (arguments.Count != 2
            || arguments[0] != "--repository"
            || string.IsNullOrWhiteSpace(arguments[1]))
        {
            throw new ArgumentException(
                "list-test-owner-assemblies requires exactly --repository value");
        }

        var manifest = EngineeringInputManifest.ReadCurrent(Path.GetFullPath(arguments[1]));
        var assemblies = manifest.Projects.Where(EngineeringInputManifest.IsTest)
            .Select(project => project.Assembly).Order(StringComparer.Ordinal).ToArray();
        if (assemblies.Length == 0)
        {
            throw new InvalidDataException(
                "list-test-owner-assemblies registered zero test assemblies");
        }

        foreach (var assembly in assemblies)
        {
            standardOutput.WriteLine(assembly);
        }

        return 0;
    }

    private static int VerifyTrx(
        VerifyTrxOptions options,
        Func<string, TestResultEvidence> evidenceLoader,
        TextWriter standardOutput)
    {
        var evidence = evidenceLoader(options.ResultsDirectory);
        if (options.RequiredAssemblies.Length != 0)
        {
            foreach (var requiredAssembly in options.RequiredAssemblies)
            {
                var assemblyExecuted = evidence.CountAssembly(requiredAssembly);
                if (assemblyExecuted == 0)
                {
                    throw new InvalidDataException(
                        $"TRX has no executed identity from required assembly {requiredAssembly}");
                }

                standardOutput.WriteLine(
                    $"ENGINEERING_BASE_FLOOR_EXECUTED assembly={requiredAssembly} "
                    + $"evidence=trx executed={assemblyExecuted}");
            }
        }
        else
        {
            standardOutput.WriteLine($"TEST_EVIDENCE_ACCEPTED evidence=trx executed={evidence.Executed}");
        }

        return 0;
    }

    private static void WritePlan(EngineeringTestPlan plan, TextWriter output)
    {
        output.WriteLine(
            $"ENGINEERING_TEST_PLAN state={plan.Kind.ToString().ToLowerInvariant()} "
            + $"changed={plan.ChangedPaths.Length} selected={plan.Projects.Length} "
            + $"reason={JsonSerializer.Serialize(plan.Reason)}");
        foreach (var path in plan.ChangedPaths)
            output.WriteLine($"ENGINEERING_TEST_INPUT path={JsonSerializer.Serialize(path)}");
        foreach (var project in plan.Projects)
        {
            output.WriteLine(
                $"ENGINEERING_TEST_PROJECT project={JsonSerializer.Serialize(project)}");
        }
    }

    private static string GitText(string repositoryRoot, params string[] arguments) =>
        GitOutput(repositoryRoot, 1024 * 1024, arguments).Trim();

    private static string GitRawText(string repositoryRoot, params string[] arguments) =>
        GitOutput(repositoryRoot, 32 * 1024 * 1024, arguments);

    private static string GitOutput(string repositoryRoot, int maximumOutputBytes, params string[] arguments)
    {
        var output = BoundedProcessRunner.Run("git", ["-C", repositoryRoot, .. arguments], repositoryRoot, BoundedProcessRunner.HangDetectionBudget, maximumOutputBytes);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput);
    }

    private static bool IsObjectId(string value, int expectedLength) =>
        value.Length == expectedLength
        && value.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static IReadOnlyList<string> GitPaths(string repositoryRoot, string @base, string? head)
    {
        var output = BoundedProcessRunner.Run(
            "git",
            ["-C", repositoryRoot, "diff", "--name-only", "-z", "--no-renames", "--diff-filter=ACDMRTUXB", @base, .. head is null ? Array.Empty<string>() : [head], "--"],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            32 * 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries);
    }

    private sealed record Options(string RepositoryRoot, string Event, string Head, string Before, bool Full, bool PlanOnly)
    {
        internal static Options Parse(IReadOnlyList<string> arguments)
        {
            var values = new Dictionary<string, string>(StringComparer.Ordinal);
            for (var index = 0; index < arguments.Count; index += 2)
            {
                if (index + 1 >= arguments.Count || !arguments[index].StartsWith("--", StringComparison.Ordinal))
                    throw new ArgumentException("options must be --name value pairs");
                if (!values.TryAdd(arguments[index], arguments[index + 1]))
                    throw new ArgumentException($"duplicate option: {arguments[index]}");
            }
            if (values.Keys.Any(static name => name is not ("--repository" or "--event" or "--head" or "--base" or "--before" or "--full" or "--plan-only")))
                throw new ArgumentException("unknown engineering planning option");
            var eventKind = Require(values, "--event");
            if (eventKind is not ("push" or "pull-request")) throw new ArgumentException("--event must be push or pull-request");
            var endpoint = eventKind == "push" ? "--before" : "--base";
            if (values.ContainsKey(eventKind == "push" ? "--base" : "--before"))
                throw new ArgumentException("push before and PR protected base are distinct input roles");
            return new(Path.GetFullPath(Require(values, "--repository")), eventKind,
                Require(values, "--head"), Require(values, endpoint), Flag(values, "--full"), Flag(values, "--plan-only"));
        }

        private static bool Flag(IReadOnlyDictionary<string, string> values, string name) =>
            values.GetValueOrDefault(name, "0") switch
            {
                "0" => false, "1" => true, _ => throw new ArgumentException(name + " must be 0 or 1"),
            };

        private static string Require(IReadOnlyDictionary<string, string> values, string name) =>
            values.TryGetValue(name, out var value) && !string.IsNullOrWhiteSpace(value)
                ? value : throw new ArgumentException($"{name} is required");
    }

    private sealed record VerifyTrxOptions(
        string ResultsDirectory,
        string[] RequiredAssemblies)
    {
        internal static VerifyTrxOptions Parse(IReadOnlyList<string> arguments)
        {
            var values = new Dictionary<string, string>(StringComparer.Ordinal);
            var requiredAssemblies = new List<string>();
            for (var index = 0; index < arguments.Count; index += 2)
            {
                if (index + 1 >= arguments.Count || !arguments[index].StartsWith("--", StringComparison.Ordinal))
                    throw new ArgumentException("verify-trx options must be --name value pairs");
                switch (arguments[index])
                {
                    case "--required-assembly":
                        if (string.IsNullOrWhiteSpace(arguments[index + 1]))
                            throw new ArgumentException("--required-assembly must not be empty");
                        requiredAssemblies.Add(arguments[index + 1]);
                        break;
                    case "--results-directory":
                        if (!values.TryAdd(arguments[index], arguments[index + 1]))
                            throw new ArgumentException($"duplicate option: {arguments[index]}");
                        break;
                    default:
                        throw new ArgumentException($"unknown verify-trx option: {arguments[index]}");
                }
            }

            if (!values.TryGetValue("--results-directory", out var resultsDirectory)
                || string.IsNullOrWhiteSpace(resultsDirectory))
            {
                throw new ArgumentException("--results-directory is required");
            }

            return new VerifyTrxOptions(
                Path.GetFullPath(resultsDirectory),
                requiredAssemblies.ToArray());
        }
    }
}
