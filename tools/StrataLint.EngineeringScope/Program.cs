using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        WriteIndented = true,
        Converters = { new JsonStringEnumConverter(JsonNamingPolicy.SnakeCaseLower, allowIntegerValues: false) },
    };

    public static int Main(string[] arguments)
    {
        try
        {
            if (arguments.FirstOrDefault() == "verify-trx")
            {
                try
                {
                    return VerifyTrx(VerifyTrxOptions.Parse(arguments.Skip(1).ToArray()));
                }
                catch (Exception exception)
                {
                    Console.Error.WriteLine($"TEST_EVIDENCE_FAILED {exception.Message}");
                    return 2;
                }
            }

            var options = Options.Parse(arguments);
            var head = GitText(options.RepositoryRoot, "rev-parse", "HEAD");
            if (options.Head != head
                || !IsObjectId(options.Base, head.Length)
                || !GitSucceeds(options.RepositoryRoot, "merge-base", "--is-ancestor", options.Base, head))
            {
                throw new InvalidOperationException(
                    "--head must equal the checked HEAD and --base must be a full object ID ancestral to HEAD");
            }

            return options.Mode switch
            {
                "plan" => Plan(options, head, options.Base),
                "execute" => Execute(options, head, options.Base),
                _ => throw new ArgumentException($"unknown mode: {options.Mode}"),
            };
        }
        catch (Exception exception)
        {
            Console.Error.WriteLine($"ENGINEERING_TEST_PLAN_FAILED {exception.Message}");
            return 2;
        }
    }

    private static int Plan(Options options, string head, string @base)
    {
        var changedPaths = GitPaths(options.RepositoryRoot, @base, head);
        EngineeringTestPlan plan;
        if (Environment.GetEnvironmentVariable("FULL") is { Length: > 0 } full)
        {
            if (full != "1") throw new InvalidOperationException("FULL must be unset or exactly 1");
            plan = EngineeringTestPlanPolicy.Full(changedPaths, "FULL=1 requests the diagnostic full plan");
        }
        else
        {
            try
            {
                plan = EngineeringTestPlanDeriver.DeriveRepository(options.RepositoryRoot, changedPaths);
            }
            catch (Exception exception)
            {
                plan = EngineeringTestPlanPolicy.Full(changedPaths, $"plan derivation failed: {exception.Message}");
            }
        }

        WriteArtifact(options.PlanFile, new EngineeringTestPlanArtifact(1, head, @base, plan));
        WritePlan(plan);
        return 0;
    }

    private static int Execute(Options options, string head, string @base)
    {
        EngineeringTestPlan plan;
        try
        {
            var artifact = JsonSerializer.Deserialize<EngineeringTestPlanArtifact>(
                File.ReadAllText(options.PlanFile, StrictUtf8),
                JsonOptions) ?? throw new InvalidDataException("plan artifact is empty");
            ValidateArtifact(artifact, head, @base);
            plan = artifact.Plan!;
        }
        catch (Exception exception)
        {
            plan = EngineeringTestPlanPolicy.Full(
                GitPaths(options.RepositoryRoot, @base, head),
                $"plan artifact failed validation: {exception.Message}");
            Console.Error.WriteLine($"ENGINEERING_TEST_PLAN_FALLBACK {exception.Message}");
        }

        WritePlan(plan);
        return EngineeringTestExecutor.Execute(plan, invocation => RunTests(options.RepositoryRoot, invocation));
    }

    private static int RunTests(string repositoryRoot, EngineeringTestInvocation invocation)
    {
        var resultsDirectory = Directory.CreateTempSubdirectory("stratalint-engineering-tests-").FullName;
        var startInfo = new ProcessStartInfo
        {
            FileName = "dotnet",
            WorkingDirectory = repositoryRoot,
            UseShellExecute = false,
        };
        foreach (var argument in new[] { "test", invocation.Target, "--configuration", "Release", "--verbosity", "normal" })
        {
            startInfo.ArgumentList.Add(argument);
        }
        if (invocation.Filter is not null)
        {
            startInfo.ArgumentList.Add("--filter");
            startInfo.ArgumentList.Add(invocation.Filter);
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
                var executed = VerifyTestEvidence(repositoryRoot, invocation, resultsDirectory);
                Console.WriteLine(
                    $"ENGINEERING_TEST_EXECUTED target={JsonSerializer.Serialize(invocation.Target)} "
                    + $"filter={JsonSerializer.Serialize(invocation.Filter)} evidence=trx executed={executed}");
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

    private static int VerifyTestEvidence(
        string repositoryRoot,
        EngineeringTestInvocation invocation,
        string resultsDirectory)
    {
        var evidence = TestResultEvidence.Load(resultsDirectory);
        var missing = invocation.ExpectedTests
            .Select(test => (Assembly: ProjectAssembly(repositoryRoot, test.ProjectPath), test.Id))
            .Where(expected => !evidence.ExecutedTests.Contains(expected))
            .Select(static expected => $"{expected.Assembly}::{expected.Id}")
            .ToArray();
        if (missing.Length != 0)
            throw new InvalidDataException($"TRX is missing planned tests: {string.Join(", ", missing)}");
        return evidence.Executed;
    }

    private static int VerifyTrx(VerifyTrxOptions options)
    {
        var evidence = TestResultEvidence.Load(options.ResultsDirectory);
        if (options.RequiredAssembly is not null)
        {
            var assemblyExecuted = evidence.CountAssembly(options.RequiredAssembly);
            if (assemblyExecuted == 0)
                throw new InvalidDataException(
                    $"TRX has no executed identity from required assembly {options.RequiredAssembly}");
            Console.WriteLine(
                $"ENGINEERING_BASE_FLOOR_EXECUTED assembly={options.RequiredAssembly} "
                + $"evidence=trx executed={assemblyExecuted}");
        }
        else
        {
            Console.WriteLine($"TEST_EVIDENCE_ACCEPTED evidence=trx executed={evidence.Executed}");
        }

        return 0;
    }

    private static string ProjectAssembly(string repositoryRoot, string projectPath)
    {
        var document = XDocument.Load(Path.Combine(repositoryRoot, projectPath), LoadOptions.None);
        return document.Descendants().FirstOrDefault(element => element.Name.LocalName == "AssemblyName")?.Value
            ?? Path.GetFileNameWithoutExtension(projectPath);
    }

    private static void ValidateArtifact(EngineeringTestPlanArtifact artifact, string head, string @base)
    {
        if (artifact.Version != 1 || artifact.Head != head || artifact.Base != @base)
            throw new InvalidDataException("plan artifact does not address the checked head and base");
        if (artifact.Plan is null || artifact.Plan.ChangedPaths.IsDefault || artifact.Plan.Tests.IsDefault
            || string.IsNullOrWhiteSpace(artifact.Plan.Reason)
            || (artifact.Plan.Kind == EngineeringTestPlanKind.Selected) != (artifact.Plan.Tests.Length != 0)
            || artifact.Plan.Tests.Any(static test => string.IsNullOrWhiteSpace(test.ProjectPath)
                || string.IsNullOrWhiteSpace(test.Id) || string.IsNullOrWhiteSpace(test.Detail)))
            throw new InvalidDataException("plan artifact does not conform to schema version 1");
    }

    private static void WritePlan(EngineeringTestPlan plan)
    {
        Console.WriteLine(
            $"ENGINEERING_TEST_PLAN state={plan.Kind.ToString().ToLowerInvariant()} "
            + $"changed={plan.ChangedPaths.Length} selected={plan.Tests.Length} "
            + $"reason={JsonSerializer.Serialize(plan.Reason)}");
        foreach (var test in plan.Tests)
        {
            Console.WriteLine(
                $"ENGINEERING_TEST_SELECTED project={JsonSerializer.Serialize(test.ProjectPath)} "
                + $"id={JsonSerializer.Serialize(test.Id)} reason={test.Reason.ToString().ToLowerInvariant()} "
                + $"detail={JsonSerializer.Serialize(test.Detail)}");
        }
    }

    private static void WriteArtifact(string path, EngineeringTestPlanArtifact artifact)
    {
        var temporary = path + ".tmp";
        File.WriteAllText(temporary, JsonSerializer.Serialize(artifact, JsonOptions) + "\n", StrictUtf8);
        File.Move(temporary, path, overwrite: true);
    }

    private static string GitText(string repositoryRoot, params string[] arguments)
    {
        var output = BoundedProcessRunner.Run("git", ["-C", repositoryRoot, .. arguments], repositoryRoot, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput).Trim();
    }

    private static bool GitSucceeds(string repositoryRoot, params string[] arguments) =>
        BoundedProcessRunner.Run(
            "git",
            ["-C", repositoryRoot, .. arguments],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024).ExitCode == 0;

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

    private sealed record EngineeringTestPlanArtifact(
        int Version,
        string Head,
        string Base,
        EngineeringTestPlan? Plan);

    private sealed record Options(string Mode, string RepositoryRoot, string Head, string Base, string PlanFile)
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

            return new Options(
                Require(values, "--mode"),
                Path.GetFullPath(Require(values, "--repository")),
                Require(values, "--head"),
                Require(values, "--base"),
                Path.GetFullPath(Require(values, "--plan-file")));
        }

        private static string Require(IReadOnlyDictionary<string, string> values, string name) =>
            values.TryGetValue(name, out var value) && !string.IsNullOrWhiteSpace(value)
                ? value
                : throw new ArgumentException($"{name} is required");
    }

    private sealed record VerifyTrxOptions(string ResultsDirectory, string? RequiredAssembly)
    {
        internal static VerifyTrxOptions Parse(IReadOnlyList<string> arguments)
        {
            var values = new Dictionary<string, string>(StringComparer.Ordinal);
            for (var index = 0; index < arguments.Count; index += 2)
            {
                if (index + 1 >= arguments.Count || !arguments[index].StartsWith("--", StringComparison.Ordinal))
                    throw new ArgumentException("verify-trx options must be --name value pairs");
                if (!values.TryAdd(arguments[index], arguments[index + 1]))
                    throw new ArgumentException($"duplicate option: {arguments[index]}");
            }

            if (!values.TryGetValue("--results-directory", out var resultsDirectory)
                || string.IsNullOrWhiteSpace(resultsDirectory))
            {
                throw new ArgumentException("--results-directory is required");
            }

            values.TryGetValue("--required-assembly", out var requiredAssembly);
            return new VerifyTrxOptions(Path.GetFullPath(resultsDirectory), requiredAssembly);
        }
    }
}
