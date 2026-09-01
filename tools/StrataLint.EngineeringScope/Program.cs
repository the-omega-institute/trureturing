using System.Diagnostics;
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

        var plan = EngineeringTestPlanPolicy.Evaluate(
            GitPaths(options.RepositoryRoot, @base, head),
            RepositoryRules.ReadSnapshotProjects(
                RevisionSnapshot(options.RepositoryRoot, @base, "protected base")),
            full == "1");
        WritePlan(plan);
        return EngineeringTestExecutor.Execute(
            plan,
            invocation => RunTests(options.RepositoryRoot, invocation));
    }

    private static int RunTests(
        string repositoryRoot,
        EngineeringTestInvocation invocation)
    {
        var resultsDirectory = Directory.CreateTempSubdirectory("stratalint-engineering-tests-").FullName;
        var startInfo = new ProcessStartInfo
        {
            FileName = "dotnet",
            WorkingDirectory = repositoryRoot,
            UseShellExecute = false,
        };
        foreach (var argument in new[] { "test", invocation.ProjectPath, "--configuration", "Release", "--verbosity", "normal" })
        {
            startInfo.ArgumentList.Add(argument);
        }
        startInfo.ArgumentList.Add("--logger");
        startInfo.ArgumentList.Add("trx;LogFilePrefix=engineering");
        startInfo.ArgumentList.Add("--results-directory");
        startInfo.ArgumentList.Add(resultsDirectory);

        try
        {
            using var process = Process.Start(startInfo) ?? throw new InvalidOperationException("could not start dotnet test");
            process.WaitForExit();
            if (process.ExitCode != 0) return process.ExitCode;

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
        SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadRevision(repositoryRoot, revision)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidDataException($"{description} snapshot is invalid: {failure.Message}"),
            _ => throw new InvalidDataException($"{description} snapshot decode returned an unknown outcome"),
        };

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
