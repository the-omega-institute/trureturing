using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class Program
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        WriteIndented = true,
        Converters = { new JsonStringEnumConverter(JsonNamingPolicy.SnakeCaseLower) },
    };

    public static int Main(string[] arguments)
    {
        try
        {
            var options = Options.Parse(arguments);
            var head = GitText(options.RepositoryRoot, "rev-parse", "HEAD");
            var @base = GitText(options.RepositoryRoot, "rev-parse", "HEAD^1");
            if (options.Head != head || options.Base != @base)
            {
                throw new InvalidOperationException("--head and --base must equal rev-parse HEAD and rev-parse HEAD^1");
            }

            return options.Mode switch
            {
                "plan" => Plan(options, head, @base),
                "execute" => Execute(options, head, @base),
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
        var artifact = JsonSerializer.Deserialize<EngineeringTestPlanArtifact>(
            File.ReadAllText(options.PlanFile, StrictUtf8),
            JsonOptions) ?? throw new InvalidDataException("plan artifact is empty");
        if (artifact.Version != 1 || artifact.Head != head || artifact.Base != @base)
        {
            throw new InvalidDataException("plan artifact does not address the checked HEAD and HEAD^1");
        }

        WritePlan(artifact.Plan);
        return EngineeringTestExecutor.Execute(artifact.Plan, invocation => RunTests(options.RepositoryRoot, invocation));
    }

    private static int RunTests(string repositoryRoot, EngineeringTestInvocation invocation)
    {
        Console.WriteLine(
            $"ENGINEERING_TEST_EXECUTED target={JsonSerializer.Serialize(invocation.Target)} "
            + $"filter={JsonSerializer.Serialize(invocation.Filter)}");
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

        using var process = Process.Start(startInfo) ?? throw new InvalidOperationException("could not start dotnet test");
        process.WaitForExit();
        return process.ExitCode;
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
        var output = BoundedProcessRunner.Run("git", ["-C", repositoryRoot, .. arguments], repositoryRoot, TimeSpan.FromSeconds(30), 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput).Trim();
    }

    private static IReadOnlyList<string> GitPaths(string repositoryRoot, string @base, string head)
    {
        var output = BoundedProcessRunner.Run(
            "git",
            ["-C", repositoryRoot, "diff", "--name-only", "-z", "--no-renames", "--diff-filter=ACDMRTUXB", @base, head, "--"],
            repositoryRoot,
            TimeSpan.FromSeconds(30),
            32 * 1024 * 1024);
        if (output.ExitCode != 0) throw new InvalidOperationException(StrictUtf8.GetString(output.StandardError).Trim());
        return StrictUtf8.GetString(output.StandardOutput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries);
    }

    private sealed record EngineeringTestPlanArtifact(
        int Version,
        string Head,
        string Base,
        EngineeringTestPlan Plan);

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
}
