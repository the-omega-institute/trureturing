using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal sealed record TestProjectActionResult(TestProjectExecution Execution, CachedTestSuccess? Success, string[] Materials);

internal static class AffectedTestExecution
{
    internal static int Run(string root, Func<string, string, string?, int> run, TextWriter output, CommonStageRecord build,
        TestEnvironmentContext? context = null)
    {
        var plan = CommonExecutionEvidence.Read<TestInputManifest>(root, AffectedTestPlan.PathName);
        AffectedTestPlan.Validate(plan);
        context ??= CommonStages.TestEnvironment(root);
        output.WriteLine("ENGINEERING_TEST_CONTEXT " + JsonSerializer.Serialize(new {
            startups = context.Startups, seconds = context.StartupSeconds, context.Identity, context.ValuesIdentity, context.Culture, context.UICulture }));
        AffectedEnvironmentObservation.Write(root, "executor-validation", plan, build.Candidate, context: context);
        if (plan.Candidate != build.Candidate) throw new InvalidDataException("current test input manifest candidate mismatch");
        var cache = new AffectedTestCache(root, output);
        var results = new List<TestProjectActionResult>();
        var invocation = Guid.NewGuid().ToString("N");
        output.WriteLine($"ENGINEERING_TEST_PLAN state=affected required_projects={plan.Projects.Length} actions={plan.Actions.Length} candidate={build.Candidate}");
        foreach (var action in plan.Actions)
            results.Add(RunProject(root, action, plan.Projects.Single(project => project.Project == action.Project), build,
                cache, context, run, output, $"{CommonExecutionEvidence.RootPath}/trx/{invocation}/{results.Count}"));
        var record = new TestExecutionRecord(3, build.Candidate, build.Round, TestProducerExecutionContext.Capture(context),
            results.Select(result => result.Execution).ToArray(),
            CommonExecutionEvidence.Materials(root, results.SelectMany(result => result.Materials)
                .Concat([AffectedTestPlan.PathName, CommonExecutionEvidence.BuildPath])));
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.TestsPath, record);
        if (record.Projects.Any(project => project.Exit != 0 || project.Error is not null)) return 1;
        // The stage, not the project executor, reconciles every required project.
        CommonExecutionEvidence.ValidateTests(root, context: context);
        cache.Save(plan with { Actions = plan.Actions.Select(action => AffectedTestPlan.BindEnvironment(action, context)).ToArray() },
            results.Select(result => result.Success).OfType<CachedTestSuccess>(), context);
        return 0;
    }

    // Production boundary shared by normal engineering and focused project verification.
    // It always launches an unfiltered native project. It cannot certify a stage.
    internal static TestProjectActionResult RunProject(string root, TestAction action, TestProjectInputs inputs,
        CommonStageRecord build, AffectedTestCache cache, TestEnvironmentContext context,
        Func<string, string, string?, int> run, TextWriter output, string relative)
    {
        if (action.Identity != AffectedTestPlan.Identity(action) || inputs.Identity != AffectedTestPlan.ProjectIdentity(inputs)
            || action.Producer != AffectedTestPlan.ProducerIdentity() || action.ProjectIdentity != inputs.Identity)
            throw new InvalidDataException("current test input manifest is invalid");
        action = AffectedTestPlan.BindEnvironment(action, context);
        var started = TimeProvider.System.GetTimestamp();
        var selection = cache.Select(action, inputs);
        if (selection.Success is { } success)
        {
            try
            {
                var restored = cache.Restore(success);
                var coverage = new TestActionCoverage("*", "reused", selection.Reason, action.Identity, success.Source.Covered, restored, success.Source);
                var execution = new TestProjectExecution(action.Project, "", 0, 0, null) { Coverage = [coverage] };
                Report(execution);
                return new(execution, success, restored);
            }
            catch (Exception exception) when (AffectedTestCache.CacheFailure(exception))
            { selection = (null, "cache-restore-failed:" + exception.Message); }
        }
        output.WriteLine("ENGINEERING_TEST_SELECTION " + JsonSerializer.Serialize(new { project = action.Project, scope = "*", reason = selection.Reason }));
        var directory = Path.Combine(root, relative);
        Directory.CreateDirectory(directory);
        var exit = 2;
        var executed = 0;
        string? failure = null;
        TestActionCoverage[] coverageRows = [];
        CachedTestSuccess? saved = null;
        try
        {
            exit = run(action.Project, directory, null);
            var evidence = TestResultEvidence.Load(directory);
            executed = evidence.Executed;
            if (evidence.CountAssembly(action.Assembly) == 0) throw new InvalidDataException("TRX belongs to a different test assembly");
            if (exit != 0) throw new InvalidDataException($"dotnet test exit={exit}");
            var trx = CommonExecutionEvidence.Materials(root, Directory.GetFiles(directory, "*.trx")
                .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')));
            var source = new TestSuccessSource(build.Candidate, build.Round,
                Environment.GetEnvironmentVariable("GITHUB_RUN_ID") ?? "local", Environment.GetEnvironmentVariable("GITHUB_RUN_ATTEMPT") ?? "local",
                Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "local", action.Identity, executed, trx);
            if (action.UsesExplicitValues)
            {
                AffectedTestCache.ValidateSource(action, source, trx.Select(material => Path.Combine(root, material.Path)).ToArray(), _ => evidence);
                saved = new(action.Project, "*", action.Identity, source);
            }
            coverageRows = [new("*", "executed", selection.Reason, action.Identity, executed, trx.Select(material => material.Path).ToArray(), source)];
        }
        catch (Exception exception) { failure = exception.Message; }
        var paths = Directory.GetFiles(directory, "*.trx").Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).ToArray();
        var record = new TestProjectExecution(action.Project, relative, exit, executed, failure) { Coverage = coverageRows };
        Report(record);
        return new(record, failure is null ? saved : null, paths);

        void Report(TestProjectExecution execution) => output.WriteLine("ENGINEERING_PROJECT_ACTION " + JsonSerializer.Serialize(new {
            project = action.Project, executed = execution.Executed,
            reused = execution.Coverage.Where(row => row.Status == "reused").Sum(row => row.Covered),
            unknown = !action.UsesExplicitValues, execution.Exit, execution.Error,
            seconds = TimeProvider.System.GetElapsedTime(started).TotalSeconds, action.Identity,
            context = action.Environment, coverage = execution.Coverage }));
    }
}
