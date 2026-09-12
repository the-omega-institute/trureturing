using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ResourceAdapterTests
{
    [Fact]
    public void PushRangeUsesEventEndpointsAcrossMultipleCommits()
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("fixtures/selected.txt", "code commit\n");
        fixture.CommitPlan();
        fixture.Write("docs/push-range.md", "docs commit\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before);
        var result = PlannerWithEnvironment(fixture, environment, "push-plan");
        Assert.True(result.Exit == 0, result.Text);
        var paths = PushScope(fixture)["changes"]!.AsArray().SelectMany(row =>
            new[] { row!["old"], row["new"] }.Where(value => value is not null).Select(value => value!["path"]!.ToString())).Distinct().Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(new[] { "docs/push-range.md", "fixtures/selected.txt" }, paths);
        Assert.Equal(new[] { "build", "filemap" }, Strings(PushSelection(fixture)["resources"]!));
        Assert.Equal("event-range", PushScope(fixture)["origin"]!["kind"]!.ToString());
    }

    [Fact]
    public void ZeroBeforeIsExplicitInitialInputEvenWhenCandidateHasParents()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        fixture.Write("fixtures/selected.txt", "initial input\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, new string('0', 40));
        var result = PlannerWithEnvironment(fixture, environment, "push-plan");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal("initial-registered-current-input", PushScope(fixture)["origin"]!["kind"]!.ToString());
        Assert.NotEmpty(PushScope(fixture)["changes"]!.AsArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PushOriginInitialTreeUsesRegisteredResourcesWithoutParentOrRemote(bool required)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(required ? ["filemap"] : []);
        var tree = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^{tree}");
        var root = SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", tree, "-m", "initial candidate");
        SharedBuildContractTests.Git(fixture.Root, "reset", "--hard", root);
        Assert.Empty(SharedBuildContractTests.Git(fixture.Root, "remote"));
        var result = PushPlan(fixture, new string('0', 40));
        Assert.True(result.Exit == 0, result.Text);
        var scope = PushScope(fixture);
        Assert.Equal("initial-registered-current-input", scope["origin"]!["kind"]!.ToString());
        Assert.Equal(new string('0', 40), scope["origin"]!["before"]!.ToString());
        Assert.Equal(root, scope["origin"]!["after"]!.ToString());
        Assert.True(scope["change_count"]!.GetValue<int>() > 1);
        Assert.Contains(scope["changes"]!.AsArray(), row => row!["new"]!["path"]!.ToString() == "fixtures/selected.txt");
        AssertPushBinding(fixture, root, tree);
        var plan = PushSelection(fixture);
        Assert.Equal(required ? new[] { "build", "filemap" } : [], Strings(plan["resources"]!));
        Assert.Equal(required ? new[] { "build", "current" } : [], Strings(plan["selected_stages"]!));
    }

    [Theory]
    [InlineData("modify")]
    [InlineData("delete")]
    [InlineData("rename")]
    [InlineData("mode")]
    public void PushUsesBothPathSidesToSelectExactlyRegisteredWork(string change)
    {
        const string oldPath = "fixtures/old name\tΩ\n.txt";
        const string newPath = "docs/new name\tΩ\n.md";
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        // Separate declarations make loss of the removed endpoint observable.
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var row = map[map.IndexOf("[[files]]", StringComparison.Ordinal)..];
        map = map[..map.IndexOf("[[files]]", StringComparison.Ordinal)] +
            string.Concat(new[] { "*", "Meta/**", "docs/*", "fixtures/*", "tools/**" }.Select(pattern =>
                row.Replace("pattern = \"**\"", "pattern = \"" + pattern + "\"", StringComparison.Ordinal)
                   .Replace("require = [\"filemap\"]", pattern == "fixtures/*" ? "require = [\"filemap\"]" : "require = []", StringComparison.Ordinal)));
        fixture.Write("Meta/FILEMAP.toml", map);
        fixture.Write(oldPath, "a registered old resource input\n");
        fixture.CommitPlan();
        var parent = fixture.Commit;
        if (change == "modify") fixture.Write(oldPath, "changed required input\n");
        else if (change == "mode") SharedBuildContractTests.Process(fixture.Root, "/bin/chmod", ["+x", oldPath]);
        else if (change == "delete") File.Delete(Path.Combine(fixture.Root, oldPath));
        else
        {
            Directory.CreateDirectory(Path.Combine(fixture.Root, "docs"));
            File.Move(Path.Combine(fixture.Root, oldPath), Path.Combine(fixture.Root, newPath));
        }
        fixture.CommitPlan();
        var result = PushPlan(fixture);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(parent, PushScope(fixture)["origin"]!["before"]!.ToString());
        Assert.Equal(fixture.Commit, PushScope(fixture)["origin"]!["after"]!.ToString());
        Assert.Equal("event-range", PushScope(fixture)["origin"]!["kind"]!.ToString());
        var plan = PushSelection(fixture);
        Assert.Equal(change == "rename" ? new[] { newPath, oldPath } : [oldPath], Strings(plan["paths"]!, "path"));
        Assert.Equal(new[] { "build", "filemap" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["steps"]!));
        fixture.Processes();
        File.Copy(PushPlanPath(fixture), fixture.Plan, true);
        File.Copy(PushScopePath(fixture), fixture.Changes, true);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(new[] { "dotnet filemap-conform" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
    }

    [Theory]
    [InlineData("shallow")]
    [InlineData("missing")]
    public void PushEndpointObjectsWorkWhenShallowAndFailWhenUnavailable(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var parent = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        if (defect == "shallow") fixture.Write(".git/shallow", fixture.Commit + "\n");
        else File.Delete(Path.Combine(fixture.Root, ".git/objects", parent[..2], parent[2..]));
        var result = PushPlan(fixture, parent);
        if (defect == "shallow")
        {
            Assert.True(result.Exit == 0, result.Text);
            Assert.Equal(parent, PushScope(fixture)["origin"]!["before"]!.ToString());
            Assert.Equal("event-range", PushScope(fixture)["origin"]!["kind"]!.ToString());
        }
        else
        {
            Assert.Equal(2, result.Exit);
            Assert.Contains("PUSH_BEFORE_UNAVAILABLE", result.Text, StringComparison.Ordinal);
            Assert.Contains(parent, result.Text, StringComparison.Ordinal);
            Assert.False(File.Exists(PushPlanPath(fixture)));
        }
    }

    [Fact]
    public void PushMissingPromisorParentFailsWithoutContactingRemote()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var parent = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        File.Delete(Path.Combine(fixture.Root, ".git/objects", parent[..2], parent[2..]));
        SharedBuildContractTests.Git(fixture.Root, "config", "remote.origin.url", "push-probe::unavailable");
        SharedBuildContractTests.Git(fixture.Root, "config", "remote.origin.promisor", "true");
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, parent);
        var helper = Path.Combine(environment["PATH"], "git-remote-push-probe");
        File.WriteAllText(helper, "#!/bin/bash\nprintf 'contacted\\n' > \"$PUSH_REMOTE_PROBE\"\nexit 1\n");
        SharedBuildContractTests.Process(fixture.Root, "/bin/chmod", ["+x", helper]);
        var contacted = Path.Combine(fixture.Root, "build/remote-contacted");
        environment["PUSH_REMOTE_PROBE"] = contacted;
        environment["GIT_NO_LAZY_FETCH"] = "0";
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(environment["PATH"], "python3"),
            ["-B", "tools/scripts/workflow/ci.py", "push-plan", "--repository", fixture.Root], environment,
            TestBudgets.WorkflowProcessHangGuard);
        Assert.Equal(2, result.Exit);
        Assert.Contains("PUSH_BEFORE_UNAVAILABLE", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(contacted), "Planning contacted the promisor remote for a missing object.");
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Fact]
    public void DirectCurrentKeepsWorkingTreeExecutionWithoutImplicitPushScheduling()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var tree = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^{tree}");
        var parentless = SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", tree, "-m", "direct current without ancestry");
        SharedBuildContractTests.Git(fixture.Root, "reset", "--hard", parentless);
        Assert.Empty(SharedBuildContractTests.Git(fixture.Root, "remote"));
        var environment = EnvironmentFor(fixture);
        environment["GITHUB_EVENT_NAME"] = "push";
        environment["GITHUB_EVENT_PATH"] = Path.Combine(fixture.Root, "build/absent-event.json");
        environment["CI_PLAN_PATH"] = "";
        environment["CI_CHANGES_PATH"] = "";
        fixture.Write("fixtures/selected.txt", "uncommitted current input\n");
        fixture.Write("tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll", "fixture");
        var dotnet = Path.Combine(environment["PATH"], "dotnet");
        File.WriteAllText(dotnet, "#!/bin/bash\nprintf '%s\\n' \"$@\" > build/native-arguments\nexit 1\n");
        SharedBuildContractTests.Process(fixture.Root, "/bin/chmod", ["+x", dotnet]);
        var result = Shell(fixture, ["current"], environment);
        Assert.True(result.Exit == 1, result.Text);
        var arguments = File.ReadAllLines(Path.Combine(fixture.Root, "build/native-arguments"));
        Assert.Contains("current", arguments);
        Assert.DoesNotContain("--plan", arguments);
        Assert.DoesNotContain("--changes", arguments);
        Assert.DoesNotContain("--base", arguments);
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Theory]
    [InlineData("candidate")]
    [InlineData("tree")]
    [InlineData("parent")]
    [InlineData("initial")]
    [InlineData("incomplete")]
    [InlineData("empty")]
    [InlineData("origin")]
    [InlineData("null-origin")]
    public void PushScopeCannotSubstituteAnotherComparison(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.Write("fixtures/selected.txt", "changed\n");
        fixture.CommitPlan();
        Assert.True(PushPlan(fixture).Exit == 0);
        var scope = PushScope(fixture);
        switch (defect)
        {
            case "candidate": scope["candidate"]!["commit"] = new string('a', 40); break;
            case "tree": scope["candidate"]!["tree"] = new string('a', 40); break;
            case "parent": scope["origin"]!["before"] = fixture.Commit; break;
            case "initial": scope["origin"]!["kind"] = "initial-registered-current-input"; scope["origin"]!["before"] = new string('0', 40); break;
            case "incomplete": scope["complete"] = false; break;
            case "empty": scope["changes"] = new JsonArray(); scope["change_count"] = 0; break;
            case "origin": scope.AsObject().Remove("origin"); break;
            case "null-origin": scope["origin"] = null; break;
        }
        File.WriteAllText(PushScopePath(fixture), scope.ToJsonString());
        var result = Planner(fixture, "plan", "--commit", fixture.Commit, "--changes", PushScopePath(fixture),
            "--output", Path.Combine(fixture.Root, "build/forged-plan.json"));
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/forged-plan.json")));
    }

    [Theory]
    [InlineData("HEAD")]
    [InlineData("0000000000000000000000000000000000000000")]
    [InlineData("parent")]
    public void PushCandidateMustBeCheckedOutImmutableHead(string candidate)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        if (candidate == "parent") candidate = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        var result = Planner(fixture, "push-plan", "--commit", candidate);
        Assert.Equal(2, result.Exit);
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NativePushCannotConsumeCallerCurrentScopeOrPartialTransport(bool partial)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        environment["GITHUB_EVENT_NAME"] = "push";
        if (partial) environment["CI_PLAN_B64"] = Encode(File.ReadAllText(fixture.Plan));
        var result = Route(fixture, "current", environment);
        Assert.Equal(2, result.Exit);
        Assert.Equal("failed", Summary(fixture, "current")["status"]!.ToString());
    }

    [Fact]
    public void CommittedPushPlanCannotAuthorizeDirtyCurrentNoWork()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        Assert.True(PushPlan(fixture).Exit == 0);
        fixture.Write("fixtures/selected.txt", "uncommitted work\n");
        var environment = EnvironmentFor(fixture);
        environment["CI_PLAN_PATH"] = PushPlanPath(fixture);
        environment["CI_CHANGES_PATH"] = PushScopePath(fixture);
        var result = Shell(fixture, ["current"], environment);
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.Equal("failed", Summary(fixture, "current")["status"]!.ToString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void PushRegistrationGapsAndConflictsNameTheConcretePath(bool conflict)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var row = map[map.IndexOf("[[files]]", StringComparison.Ordinal)..];
        var patterns = conflict ? new[] { "**", "missing/**" } : new[] { "*", "Meta/**", "fixtures/**", "tools/**" };
        fixture.Write("Meta/FILEMAP.toml", map[..map.IndexOf("[[files]]", StringComparison.Ordinal)] +
            string.Concat(patterns.Select(pattern => row.Replace("pattern = \"**\"", "pattern = \"" + pattern + "\"", StringComparison.Ordinal))));
        fixture.CommitPlan();
        fixture.Write("missing/registered-later.md", "no inferred ownership\n");
        fixture.CommitPlan();
        var result = PushPlan(fixture);
        Assert.Equal(2, result.Exit);
        Assert.Contains("missing/registered-later.md: FILEMAP match count " + (conflict ? "2" : "0"), result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Theory]
    [InlineData("unterminated")]
    [InlineData("rename-side")]
    [InlineData("encoding")]
    public void MalformedNativeGitInputFailsBeforePlanning(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1"));
        var shim = Path.Combine(environment["PATH"], "git");
        var realGit = File.ResolveLinkTarget(shim, true)!.FullName;
        File.Delete(shim);
        var payload = defect switch
        {
            "unterminated" => "printf 'unterminated'",
            "encoding" => "printf '\\377\\0'",
            _ => "printf '%s\\0' ':100644 100644 " + new string('a', 40) + " " + new string('b', 40) + " R100' 'fixtures/old.txt'",
        };
        File.WriteAllText(shim, "#!/bin/bash\nif [[ \"$1\" == --no-replace-objects && \"$2\" == diff ]]; then\n" + payload +
            "\nelse exec \"$PUSH_REAL_GIT\" \"$@\"; fi\n");
        SharedBuildContractTests.Process(fixture.Root, "/bin/chmod", ["+x", shim]);
        environment["PUSH_REAL_GIT"] = realGit;
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(environment["PATH"], "python3"),
            ["-B", "tools/scripts/workflow/ci.py", "push-plan", "--repository", fixture.Root], environment,
            TestBudgets.WorkflowProcessHangGuard);
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Fact]
    public void LocalPushPreflightUsesTheSameNoWorkScopeBeforeAnySdkOrCache()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        foreach (var path in new[] { "tools/scripts/preflight.sh", "tools/scripts/ci-stage.sh" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        fixture.CommitPlan();
        fixture.Write("fixtures/selected.txt", "documentation change\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment["MODE"] = "push";
        environment["BASE"] = "";
        environment["GITHUB_EVENT_NAME"] = "";
        environment["CI_PLAN_PATH"] = "";
        environment["CI_CHANGES_PATH"] = "";
        var result = SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["tools/scripts/preflight.sh"],
            environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        foreach (var stage in new[] { "engineering", "current" })
        {
            var summary = Summary(fixture, stage);
            Assert.Equal("not-required", summary["status"]!.ToString());
            Assert.Empty(summary["steps"]!.AsArray());
            Assert.Empty(summary["artifacts"]!.AsArray());
            Assert.Null(summary["base_sha"]);
        }
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/delta-result.json")));
        AssertPushBinding(fixture, fixture.Commit, null);
    }

    [Theory]
    [InlineData("build", "event-range", false)]
    [InlineData("engineering", "event-range", true)]
    [InlineData("current", "local-current-input", false)]
    [InlineData("current", "local-current-input", true)]
    [InlineData("build", "current", true)]
    public void NativeStageRejectsCoherentReplacementScope(string stage, string replacement, bool serialized)
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("fixtures/selected.txt", "required committed code\n");
        fixture.CommitPlan();
        // Produce a genuinely valid replacement through the public non-native
        // interface: rehashing corrupted JSON alone would not exercise authority.
        if (replacement != "current")
        {
            var replacementEnvironment = EnvironmentFor(fixture);
            if (replacement == "event-range") SetPushEvent(fixture, replacementEnvironment, fixture.Commit);
            var result = PlannerWithEnvironment(fixture, replacementEnvironment, "push-plan");
            Assert.True(result.Exit == 0, result.Text);
        }
        var environment = EnvironmentFor(fixture);
        var plan = replacement == "current" ? fixture.Plan : PushPlanPath(fixture);
        var changes = replacement == "current" ? fixture.Changes : PushScopePath(fixture);
        environment["CI_PLAN_PATH"] = plan;
        environment["CI_CHANGES_PATH"] = changes;
        if (serialized)
        {
            environment["CI_PLAN_B64"] = Encode(File.ReadAllText(plan));
            environment["CI_CHANGES_B64"] = Encode(File.ReadAllText(changes));
        }
        SetPushEvent(fixture, environment, before);
        var routed = Route(fixture, stage, environment);
        Assert.Equal(2, routed.Exit);
        Assert.Contains("native push", routed.Text, StringComparison.Ordinal);
        Assert.Equal("failed", Summary(fixture, stage)["status"]!.ToString());
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/" + stage + "-no-work.json")));
    }

    [Theory]
    [InlineData("cli")]
    [InlineData("environment")]
    [InlineData("partial")]
    public void NativePushEndpointsCannotBeOverridden(string source)
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("fixtures/selected.txt", "code requiring work\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before);
        if (source != "cli") environment["CI_PUSH_BEFORE"] = fixture.Commit;
        if (source == "environment") environment["CI_PUSH_AFTER"] = fixture.Commit;
        var result = PlannerWithEnvironment(fixture, environment, "push-plan",
            source == "cli" ? ["--before", fixture.Commit, "--after", fixture.Commit] : []);
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Theory]
    [InlineData("missing-before")]
    [InlineData("missing-after")]
    [InlineData("invalid-before")]
    [InlineData("invalid-after")]
    [InlineData("wrong-after")]
    [InlineData("zero-after")]
    [InlineData("unavailable-before")]
    [InlineData("tree-before")]
    [InlineData("missing-event")]
    public void NativeFreshStageRejectsInvalidEventInput(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var before = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1");
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before);
        var eventPath = environment["GITHUB_EVENT_PATH"];
        var data = JsonNode.Parse(File.ReadAllText(eventPath))!;
        switch (defect)
        {
            case "missing-before": data.AsObject().Remove("before"); break;
            case "missing-after": data.AsObject().Remove("after"); break;
            case "invalid-before": data["before"] = "HEAD"; break;
            case "invalid-after": data["after"] = "HEAD"; break;
            case "wrong-after": data["after"] = before; break;
            case "zero-after": data["after"] = new string('0', 40); break;
            case "unavailable-before": data["before"] = new string('a', 40); break;
            case "tree-before": data["before"] = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^{tree}"); break;
        }
        File.WriteAllText(eventPath, data.ToJsonString());
        if (defect == "missing-event") File.Delete(eventPath);
        environment["CI_PLAN_PATH"] = "";
        environment["CI_CHANGES_PATH"] = "";
        var result = Route(fixture, "build", environment);
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.Equal("failed", Summary(fixture, "build")["status"]!.ToString());
        Assert.False(File.Exists(PushPlanPath(fixture)));
    }

    [Fact]
    public void ForcePushComparesNonancestorTreesAndKeepsRemovedRequiredPaths()
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        var tree = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^{tree}");
        var unrelated = SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", tree, "-m", "unrelated force candidate");
        SharedBuildContractTests.Git(fixture.Root, "reset", "--hard", unrelated);
        File.Delete(Path.Combine(fixture.Root, "fixtures/selected.txt"));
        fixture.Write("docs/moved.md", "registered input\n");
        SharedBuildContractTests.Git(fixture.Root, "add", ".");
        SharedBuildContractTests.Git(fixture.Root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "-qm", "force endpoint");
        var head = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD");
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before, head);
        var result = PlannerWithEnvironment(fixture, environment, "push-plan");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "docs/moved.md", "fixtures/selected.txt" }, Strings(PushSelection(fixture)["paths"]!, "path"));
        Assert.Equal(new[] { "build", "filemap" }, Strings(PushSelection(fixture)["resources"]!));
    }

    [Fact]
    public void NativeDocsOnlyStagesProduceHonestNoWorkWithoutHeavyTools()
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("docs/note.md", "docs only\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before);
        environment["CI_PLAN_PATH"] = PushPlanPath(fixture);
        environment["CI_CHANGES_PATH"] = PushScopePath(fixture);
        foreach (var stage in new[] { "build", "engineering", "current" })
        {
            var result = Route(fixture, stage, environment);
            Assert.True(result.Exit == 0, result.Text);
            Assert.Equal("not-required", Summary(fixture, stage)["status"]!.ToString());
            Assert.Empty(Summary(fixture, stage)["artifacts"]!.AsArray());
            Assert.Empty(Summary(fixture, stage)["steps"]!.AsArray());
        }
        Assert.Empty(Strings(PushSelection(fixture)["resources"]!));
        Assert.Empty(Strings(PushSelection(fixture)["cache_layers"]!));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
    }

    [Fact]
    public void NativeIdenticalEndpointsProduceCompleteEmptyNoWork()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, fixture.Commit);
        environment["CI_PLAN_PATH"] = PushPlanPath(fixture);
        environment["CI_CHANGES_PATH"] = PushScopePath(fixture);
        foreach (var stage in new[] { "build", "engineering", "current" })
        {
            var result = Route(fixture, stage, environment);
            Assert.True(result.Exit == 0, result.Text);
            Assert.Equal("not-required", Summary(fixture, stage)["status"]!.ToString());
            Assert.Empty(Summary(fixture, stage)["artifacts"]!.AsArray());
            Assert.Empty(Summary(fixture, stage)["steps"]!.AsArray());
        }
        var scope = PushScope(fixture);
        Assert.Equal("event-range", scope["origin"]!["kind"]!.ToString());
        Assert.Equal(fixture.Commit, scope["origin"]!["before"]!.ToString());
        Assert.Equal(fixture.Commit, scope["origin"]!["after"]!.ToString());
        Assert.True(scope["complete"]!.GetValue<bool>());
        Assert.Equal(0, scope["change_count"]!.GetValue<int>());
        Assert.Empty(scope["changes"]!.AsArray());
        Assert.Empty(Strings(PushSelection(fixture)["resources"]!));
        Assert.Empty(Strings(PushSelection(fixture)["cache_layers"]!));
        Assert.Equal("not-applicable", PushSelection(fixture)["stages"]!["delta"]!["status"]!.ToString());
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
    }

    [Fact]
    public void NativePlanRejectsCheckoutAdvanceBeforeCurrent()
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("docs/first.md", "first candidate documentation\n");
        fixture.CommitPlan();
        var originalHead = fixture.Commit;
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, before);
        Assert.True(PlannerWithEnvironment(fixture, environment, "push-plan").Exit == 0);
        Assert.Empty(Strings(PushSelection(fixture)["resources"]!));
        fixture.Write("fixtures/selected.txt", "new required candidate input\n");
        fixture.CommitPlan();
        Assert.NotEqual(originalHead, fixture.Commit);
        environment["CI_PLAN_PATH"] = PushPlanPath(fixture);
        environment["CI_CHANGES_PATH"] = PushScopePath(fixture);
        File.Delete(Path.Combine(fixture.Root, "build/adapter-output"));
        var result = Route(fixture, "current", environment);
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.Contains("push event after does not match checked-out HEAD", result.Text, StringComparison.Ordinal);
        Assert.Equal("failed", Summary(fixture, "current")["status"]!.ToString());
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/adapter-output")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath)));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
    }

    [Fact]
    public void NativeCommonRunnerRejectsAValidPlanForAnotherEvent()
    {
        using var fixture = LocalFixture();
        var before = fixture.Commit;
        fixture.Write("fixtures/selected.txt", "required code\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        SetPushEvent(fixture, environment, fixture.Commit);
        Assert.True(PlannerWithEnvironment(fixture, environment, "push-plan").Exit == 0);
        SetPushEvent(fixture, environment, before);
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = SharedBuildContractTests.Process(fixture.Root, executable,
            ["current", "--repository", fixture.Root, "--plan", PushPlanPath(fixture), "--changes", PushScopePath(fixture)],
            environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.Equal(2, result.Exit);
        Assert.Contains("native push", result.Text, StringComparison.Ordinal);
        Assert.Equal("failed", Summary(fixture, "current")["status"]!.ToString());
    }

    [Fact]
    public void ReusablePrPlanKeepsItsCandidateRoleUnderAmbientPushEvent()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var environment = EnvironmentFor(fixture);
        environment["GITHUB_EVENT_NAME"] = "push";
        environment["GITHUB_EVENT_PATH"] = Path.Combine(fixture.Root, "build/absent-event.json");
        environment["CI_WORKFLOW_INPUTS"] = new JsonObject { ["candidate_sha"] = fixture.Commit }.ToJsonString();
        var result = Route(fixture, "current", environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal("pr", Summary(fixture, "current")["scope"]!["mode"]!.ToString());
    }

    private static void SetPushEvent(ResourceRouteTests.ResourceFixture fixture, Dictionary<string, string> environment,
        string before, string? after = null)
    {
        var eventPath = Path.Combine(fixture.Root, "build/push-event.json");
        File.WriteAllText(eventPath, new JsonObject {
            ["before"] = before, ["after"] = after ?? SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD"),
            // Event commit/path lists are intentionally incomplete: endpoints own scope.
            ["commits"] = new JsonArray(),
        }.ToJsonString());
        environment["GITHUB_EVENT_NAME"] = "push";
        environment["GITHUB_EVENT_PATH"] = eventPath;
    }

    private static void AssertPushBinding(ResourceRouteTests.ResourceFixture fixture, string commit, string? tree)
    {
        var scope = PushScope(fixture);
        Assert.Equal("push", scope["mode"]!.ToString());
        Assert.Equal(commit, scope["candidate"]!["commit"]!.ToString());
        Assert.Equal(tree, scope["candidate"]!["tree"]?.ToString());
        Assert.True(scope["complete"]!.GetValue<bool>());
        Assert.Null(scope["base"]);
        Assert.Null(scope["head"]);
        Assert.Equal("not-applicable", PushSelection(fixture)["stages"]!["delta"]!["status"]!.ToString());
    }
    private static string[] Strings(JsonNode rows, string? field = null) =>
        rows.AsArray().Select(row => (field is null ? row : row![field])!.ToString()).ToArray();
    private static string PushPlanPath(ResourceRouteTests.ResourceFixture fixture) => Path.Combine(fixture.Root, "build/ci/plan.json");
    private static string PushScopePath(ResourceRouteTests.ResourceFixture fixture) => Path.Combine(fixture.Root, "build/ci/changes.json");
    private static JsonNode PushSelection(ResourceRouteTests.ResourceFixture fixture) => JsonNode.Parse(File.ReadAllText(PushPlanPath(fixture)))!;
    private static JsonNode PushScope(ResourceRouteTests.ResourceFixture fixture) => JsonNode.Parse(File.ReadAllText(PushScopePath(fixture)))!;
    private static (int Exit, string Text) PushPlan(ResourceRouteTests.ResourceFixture fixture, string? eventBefore = null)
    {
        var parents = eventBefore is null ? SharedBuildContractTests.Git(fixture.Root, "show", "-s", "--format=%P", fixture.Commit) : "";
        var before = eventBefore ?? (parents.Length == 0 ? new string('0', 40) : parents.Split(' ', StringSplitOptions.RemoveEmptyEntries)[0]);
        var environment = EnvironmentFor(fixture);
        if (eventBefore is null && !string.IsNullOrEmpty(SharedBuildContractTests.Git(fixture.Root, "status", "--porcelain", "--untracked-files=all")))
            return PlannerWithEnvironment(fixture, environment, "push-plan");
        SetPushEvent(fixture, environment, before);
        return PlannerWithEnvironment(fixture, environment, "push-plan");
    }
    private static (int Exit, string Text) Planner(ResourceRouteTests.ResourceFixture fixture, string command, params string[] arguments)
    {
        return PlannerWithEnvironment(fixture, EnvironmentFor(fixture), command, arguments);
    }
    private static (int Exit, string Text) PlannerWithEnvironment(ResourceRouteTests.ResourceFixture fixture,
        Dictionary<string, string> environment, string command, params string[] arguments)
    {
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", command,
            "--repository", fixture.Root, .. arguments], environment, TestBudgets.WorkflowProcessHangGuard);
        if (Environment.GetEnvironmentVariable("CI_PUSH_ORIGIN_EVIDENCE") is { Length: > 0 } evidence)
            File.AppendAllText(evidence, new JsonObject {
                ["command"] = command, ["exit"] = result.Exit, ["output"] = result.Text,
                ["scope"] = File.Exists(PushScopePath(fixture)) ? PushScope(fixture) : null,
                ["plan"] = File.Exists(PushPlanPath(fixture)) ? PushSelection(fixture) : null,
            }.ToJsonString() + "\n");
        return result;
    }
}
