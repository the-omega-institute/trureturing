using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    public static int Main(string[] arguments) =>
        arguments.FirstOrDefault() == "self-lock-probe"
            ? SelfLockProbeProgram.Run(arguments.Skip(1).ToArray())
            : Run(arguments, TestResultEvidence.Load, Console.Out, Console.Error);

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
            var head = GitText(options.RepositoryRoot, "rev-parse", "HEAD");
            var @base = GitText(options.RepositoryRoot, "rev-parse", "HEAD^1");
            if (options.Head != head
                || options.Base != @base
                || !IsObjectId(options.Base, head.Length))
            {
                throw new InvalidOperationException(
                    "--head must equal the checked HEAD and --base must equal the checked HEAD^1");
            }

            return Execute(options, head, @base);
        }
        catch (Exception exception)
        {
            standardError.WriteLine($"ENGINEERING_TEST_PLAN_FAILED {exception.Message}");
            return 2;
        }
    }

    private static int Execute(Options options, string head, string @base)
    {
        var full = Environment.GetEnvironmentVariable("FULL");
        if (full is { Length: > 0 } && full != "1")
        {
            throw new InvalidOperationException("FULL must be unset or exactly 1");
        }

        var changedPaths = GitPaths(options.RepositoryRoot, @base, head);
        var protectedBaseRaw = GitRepositorySnapshotReader.ReadRevision(options.RepositoryRoot, @base);
        var admissionPlane = full == "1"
            ? null
            : AdmissionPlanePolicy.Evaluate(protectedBaseRaw, changedPaths);
        if (admissionPlane is { IsAdmissible: false })
        {
            throw new InvalidDataException(
                $"{admissionPlane.Code} {admissionPlane.Path}: {admissionPlane.Message}");
        }

        var protectedBase = DecodeSnapshot(
            full == "1" || admissionPlane?.Classification is AdmissionPlaneClassification.Bootstrap
                ? WithoutFileMap(protectedBaseRaw)
                : protectedBaseRaw,
            "protected base");
        var candidate = RevisionSnapshot(options.RepositoryRoot, head, "candidate");
        if (full == "1" || admissionPlane!.RequiresFullEngineering())
        {
            var fullPlan = EngineeringTestPlanPolicy.EvaluateOrdinary(
                changedPaths,
                RepositoryRules.ReadSnapshotProjects(protectedBase),
                RepositoryRules.ReadSnapshotProjects(candidate),
                full: true);
            if (full != "1")
            {
                fullPlan = fullPlan with
                {
                    Reason = $"protected-base admission plane "
                        + $"{admissionPlane!.Classification!.Value.ToString().ToLowerInvariant()} "
                        + "requires full engineering",
                };
            }
            return ExecutePlan(
                options.RepositoryRoot,
                fullPlan);
        }

        var protectedBaseController = ControllerClosure.Derive(protectedBase);
        var candidateController = ControllerClosure.Derive(candidate);
        var plan = EngineeringTestPlanPolicy.Evaluate(
            changedPaths,
            protectedBase,
            candidate,
            protectedBaseController.EvaluatorPaths,
            candidateController.EvaluatorPaths);
        return ExecutePlan(options.RepositoryRoot, plan);
    }

    private static int ExecutePlan(string repositoryRoot, EngineeringTestPlan plan)
    {
        WritePlan(plan);
        return EngineeringTestExecutor.Execute(
            plan,
            invocation => RunTests(repositoryRoot, invocation));
    }

    private static int RunTests(
        string repositoryRoot,
        EngineeringTestInvocation invocation)
    {
        var evidenceRoot = Environment.GetEnvironmentVariable("ENGINEERING_TRX_DIRECTORY");
        var preserveEvidence = !string.IsNullOrWhiteSpace(evidenceRoot);
        var resultsDirectory = preserveEvidence
            ? Path.Combine(
                Path.GetFullPath(evidenceRoot!),
                Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(invocation.ProjectPath)))
                    .ToLowerInvariant())
            : Directory.CreateTempSubdirectory("stratalint-engineering-tests-").FullName;
        if (preserveEvidence)
        {
            if (Directory.Exists(resultsDirectory)) Directory.Delete(resultsDirectory, recursive: true);
            Directory.CreateDirectory(resultsDirectory);
        }
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
                result = Run(noBuild: false);
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
            if (!preserveEvidence) Directory.Delete(resultsDirectory, recursive: true);
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
            "normal",
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

        var snapshot = RepositoryRules.ReadTrackedProjects(Path.GetFullPath(arguments[1]));
        var assemblies = RepositoryRules.CalculateOwnerAssemblies(snapshot);
        if (assemblies.Length == 0)
        {
            throw new InvalidDataException(
                "list-test-owner-assemblies derived zero owner assemblies");
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

    private static void WritePlan(EngineeringTestPlan plan)
    {
        Console.WriteLine(
            $"ENGINEERING_TEST_PLAN state={plan.Kind.ToString().ToLowerInvariant()} "
            + $"changed={plan.ChangedPaths.Length} selected={plan.Projects.Length} "
            + $"reason={JsonSerializer.Serialize(plan.Reason)}");
        foreach (var project in plan.Projects)
        {
            Console.WriteLine(
                $"ENGINEERING_TEST_PROJECT project={JsonSerializer.Serialize(project)}");
        }
    }

    private static string GitText(string repositoryRoot, params string[] arguments)
    {
        var output = BoundedProcessRunner.Run("git", ["-C", repositoryRoot, .. arguments], repositoryRoot, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput).Trim();
    }

    private static bool IsObjectId(string value, int expectedLength) =>
        value.Length == expectedLength
        && value.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static IReadOnlyList<string> GitPaths(string repositoryRoot, string @base, string head)
    {
        var output = BoundedProcessRunner.Run(
            "git",
            ["-C", repositoryRoot, "diff", "--name-only", "-z", "--no-renames", "--diff-filter=ACDMRTUXB", @base, head, "--"],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            32 * 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries);
    }

    private static RepositorySnapshot RevisionSnapshot(
        string repositoryRoot,
        string revision,
        string description) =>
        DecodeSnapshot(GitRepositorySnapshotReader.ReadRevision(repositoryRoot, revision), description);

    private static RepositorySnapshot DecodeSnapshot(
        RawRepositorySnapshot raw,
        string description) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidDataException($"{description} snapshot is invalid: {failure.Message}"),
            _ => throw new InvalidDataException($"{description} snapshot decode returned an unknown outcome"),
        };

    private static RawRepositorySnapshot WithoutFileMap(RawRepositorySnapshot snapshot) =>
        RawRepositorySnapshot.Create(snapshot.Entries.Where(
            static entry => entry.Path != AdmissionPlanePolicy.FileMapPath));

    private sealed record Options(string RepositoryRoot, string Head, string Base)
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
            if (values.Count != 3
                || values.Keys.Any(static name => name is not "--repository" and not "--head" and not "--base"))
            {
                throw new ArgumentException("options must be exactly --repository, --head, and --base");
            }

            return new Options(
                Path.GetFullPath(Require(values, "--repository")),
                Require(values, "--head"),
                Require(values, "--base"));
        }

        private static string Require(IReadOnlyDictionary<string, string> values, string name) =>
            values.TryGetValue(name, out var value) && !string.IsNullOrWhiteSpace(value)
                ? value
                : throw new ArgumentException($"{name} is required");
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
