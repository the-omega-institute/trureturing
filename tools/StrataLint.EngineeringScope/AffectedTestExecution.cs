using System.Text.Json;

namespace StrataLint.EngineeringScope;

internal static class AffectedTestExecution
{
    internal static int Run(string root, Func<string, string, string?, int> run, TextWriter output, CommonStageRecord build)
    {
        var plan = CommonExecutionEvidence.Read<TestInputManifest>(root, AffectedTestPlan.PathName);
        AffectedTestPlan.Validate(plan);
        var producer = AffectedTestPlan.ProducerIdentity();
        var environment = AffectedTestPlan.EnvironmentIdentity();
        if (plan.Candidate != build.Candidate || plan.Actions.Any(action =>
                action.Producer != producer || action.Environment != environment))
            throw new InvalidDataException("current test input manifest is invalid or belongs to a different environment");
        var cache = new AffectedTestCache(root, output);
        var records = new List<TestProjectExecution>();
        var successes = new List<CachedTestSuccess>();
        var materials = new HashSet<string>(StringComparer.Ordinal) { AffectedTestPlan.PathName, CommonExecutionEvidence.BuildPath };
        var invocation = Guid.NewGuid().ToString("N");
        var chosen = plan.Actions.Select(action => (Action: action, Selection: cache.Select(action, plan.Projects.Single(project => project.Project == action.Project)))).ToArray();
        output.WriteLine($"ENGINEERING_TEST_PLAN state=affected required_projects={chosen.Select(item => item.Action.Project).Distinct().Count()}"
            + $" selected_scopes={chosen.Count(item => item.Selection.Success is null)} reused_scopes={chosen.Count(item => item.Selection.Success is not null)} candidate={build.Candidate}");
        var removed = cache.Seed?.Manifest.Actions.Where(previous => !plan.Actions.Any(action => action.Project == previous.Project && action.Scope == previous.Scope)) ?? [];
        output.WriteLine("ENGINEERING_TEST_REMOVED_SCOPES " + JsonSerializer.Serialize(removed.Select(action => new { action.Project, action.Scope, removed_inputs = action.Inputs, removed_edges = action.Edges })));
        output.WriteLine("ENGINEERING_TEST_REMOVED_PROJECTS " + JsonSerializer.Serialize(cache.Seed?.Manifest.Projects
            .Where(previous => !plan.Projects.Any(project => project.Project == previous.Project)) ?? []));
        foreach (var group in chosen.GroupBy(item => item.Action.Project))
        {
            var coverage = new List<TestActionCoverage>();
            var selected = new List<(TestAction Action, string Reason)>();
            foreach (var (action, selection) in group)
            {
                if (selection.Success is not { } success) { selected.Add((action, selection.Reason)); continue; }
                try
                {
                    var restored = cache.Restore(success);
                    foreach (var path in restored) materials.Add(path);
                    coverage.Add(new(action.Scope, "reused", selection.Reason, action.Identity, success.Source.Covered, restored, success.Source));
                    successes.Add(success);
                }
                catch (Exception exception) when (AffectedTestCache.CacheFailure(exception))
                { selected.Add((action, "cache-restore-failed:" + exception.Message)); }
            }
            var relative = $"{CommonExecutionEvidence.RootPath}/trx/{invocation}/{records.Count}";
            var directory = Path.Combine(root, relative);
            var exit = 0;
            var executed = 0;
            string? failure = null;
            if (selected.Count != 0)
            {
                Directory.CreateDirectory(directory);
                var full = selected.Count == group.Count() || selected.Any(item => item.Action.Scope == "*");
                var filter = full ? null : string.Join('|', selected.SelectMany(item => item.Action.Methods)
                    .Select(method => "FullyQualifiedName=" + method));
                foreach (var item in selected) output.WriteLine("ENGINEERING_TEST_SELECTION " + JsonSerializer.Serialize(new {
                    project = group.Key, scope = item.Action.Scope, reason = item.Reason }));
                output.WriteLine($"ENGINEERING_TEST_PROJECT project={JsonSerializer.Serialize(group.Key)} filter={JsonSerializer.Serialize(filter)}");
                try
                {
                    exit = run(group.Key, directory, filter);
                    var evidence = TestResultEvidence.Load(directory);
                    executed = evidence.Executed;
                    if (evidence.CountAssembly(group.First().Action.Assembly) == 0)
                        throw new InvalidDataException("TRX belongs to a different test assembly");
                    if (exit != 0) failure = $"dotnet test exit={exit}";
                    var trx = CommonExecutionEvidence.Materials(root, Directory.GetFiles(directory, "*.trx")
                        .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')));
                    foreach (var material in trx) materials.Add(material.Path);
                    if (filter is not null && evidence.MethodCounts.Keys.Any(method => !selected.Any(item => item.Action.Methods.Contains(method, StringComparer.Ordinal))))
                        throw new InvalidDataException("test adapter executed identities outside the selected scopes");
                    foreach (var (action, reason) in selected)
                    {
                        var count = action.Scope == "*" ? executed : action.Methods.Sum(method => evidence.MethodCounts.GetValueOrDefault(method));
                        if (action.Methods.Any(method => !evidence.MethodCounts.ContainsKey(method) && !evidence.SkippedMethods.Contains(method)))
                            throw new InvalidDataException("test adapter left a required method uncovered: " + action.Scope);
                        var source = new TestSuccessSource(build.Candidate, build.Round,
                            Environment.GetEnvironmentVariable("GITHUB_RUN_ID") ?? "local", Environment.GetEnvironmentVariable("GITHUB_RUN_ATTEMPT") ?? "local",
                            Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "local", action.Identity, count, trx);
                        coverage.Add(new(action.Scope, failure is null ? "executed" : "failed", reason, action.Identity, count,
                            trx.Select(material => material.Path).ToArray(), source));
                        if (failure is null && action.Unknown.Length == 0 && count > 0 && action.Methods.All(evidence.MethodCounts.ContainsKey)
                            && !action.Methods.Any(evidence.SkippedMethods.Contains)) successes.Add(new(action.Project, action.Scope, action.Identity, source));
                    }
                    // Discovery outside the native bound map invalidates reuse for
                    // this project. It remains covered by this real full execution.
                    if (full && evidence.MethodCounts.Keys.Concat(evidence.SkippedMethods).Any(method => !group.Any(item => item.Action.Methods.Contains(method, StringComparer.Ordinal))))
                    {
                        successes.RemoveAll(success => success.Project == group.Key);
                        output.WriteLine("ENGINEERING_TEST_UNKNOWN project=" + group.Key + " reason=adapter-unmapped-identities");
                    }
                }
                catch (Exception exception) { failure = exception.Message; }
                finally
                {
                    // Keep failed/malformed raw TRX in the unsuccessful receipt too.
                    foreach (var path in Directory.GetFiles(directory, "*.trx")) materials.Add(Path.GetRelativePath(root, path).Replace('\\', '/'));
                }
            }
            foreach (var entry in coverage) output.WriteLine("ENGINEERING_TEST_COVERAGE " + JsonSerializer.Serialize(new {
                project = group.Key, scope = entry.Scope, status = entry.Status, reason = entry.Reason, covered = entry.Covered,
                original_candidate = entry.Source.Candidate, original_round = entry.Source.Round }));
            records.Add(new(group.Key, selected.Count == 0 ? "" : relative, exit, executed, failure) { Coverage = coverage.OrderBy(entry => entry.Scope, StringComparer.Ordinal).ToArray() });
        }
        var record = new TestExecutionRecord(2, build.Candidate, build.Round, records.ToArray(), CommonExecutionEvidence.Materials(root, materials));
        CommonExecutionEvidence.Write(root, CommonExecutionEvidence.TestsPath, record);
        // Failed computation is never a cache miss. Preserve its evidence and
        // return failure; never publish successes from an incomplete round.
        if (records.Any(project => project.Exit != 0 || project.Error is not null)) return 1;
        CommonExecutionEvidence.ValidateTests(root);
        cache.Save(plan, successes);
        return 0;
    }
}
