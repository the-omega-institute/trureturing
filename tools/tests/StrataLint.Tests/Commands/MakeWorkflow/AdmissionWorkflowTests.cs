using StrataLint.Engine;
using YamlDotNet.RepresentationModel;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

[Collection("Engineering execution boundary")]
public sealed partial class AdmissionWorkflowTests
{
    private static readonly string SharedAdmissionWorkflow = AdmissionWorkflow();

    // elan 从上游拉二进制,那一跳会间歇失败。两处安装都必须重试,且 elan 的缓存保存
    // 不得挂在 success() 上:装成功就该存,否则一次下载失败会让 job 红、缓存不写、
    // 下次继续 miss —— 故障自我延续。2026-08-13 实测:最近 10 个 run 里 2 个撞它,
    // dev push 上那次还连带 skip 了 admission(needs: lean-inspect)。
    [Fact]
    public void ElanInstallRetriesAndItsCacheSaveDoesNotHangOnJobSuccess()
    {
        const string installerPath = "tools/scripts/workflow/install-lean-toolchain.sh";
        var workflow = AdmissionWorkflow();
        var installer = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), installerPath));

        // 安装算法只在脚本实现一次,两个 CI 步骤都从候选树调用它。
        Assert.Single(Regex.Matches(installer, @"elan-init\.sh"));
        Assert.Single(Regex.Matches(installer, @"elan_install_with_retry\(\) \{"));
        // 数的是行首直接调用(与 Dispatch parity 扫描器同口径),不数路径字面量——
        // 调用前的具名缺席检查也引用同一路径,那不是第三次调用。
        Assert.Equal(
            2,
            Regex.Matches(
                workflow,
                "(?m)^[ \\t]*\"" + Regex.Escape($"$GITHUB_WORKSPACE/candidate/{installerPath}") + "\"",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking).Count);
        Assert.DoesNotContain("elan-init.sh", workflow, StringComparison.Ordinal);

        // 调用形是行为投影的一部分:engineering 必须把 elan 写进 GITHUB_PATH 供后续 step 用,
        // lean-inspect 不写(它在同一 step 内自己拼 PATH)。只数调用次数抓不住这两条。
        Assert.Contains(
            $"\"$GITHUB_WORKSPACE/candidate/{installerPath}\" \"$LEAN_TOOLCHAIN_FILE\" --github-path \"$GITHUB_PATH\"",
            workflow,
            StringComparison.Ordinal);
        Assert.Contains(
            $"\"$GITHUB_WORKSPACE/candidate/{installerPath}\" candidate/lean-toolchain\n",
            workflow,
            StringComparison.Ordinal);

        // 工具链下载是第二个网络跳,单独失败过(releases.lean-lang.org 返回空响应),
        // 所以它也必须走重试,而不是裸 elan toolchain install。
        Assert.Single(Regex.Matches(installer, @"elan_toolchain_with_retry\(\) \{"));
        Assert.DoesNotContain("\"$HOME/.elan/bin/elan\" toolchain install \"$toolchain\"", installer, StringComparison.Ordinal);

        // 每一处 ~/.elan 的 restore 都必须有前缀回退。两个 job 的精确 key 由不同表达式算出
        // (单文件 sha256 vs hashFiles 两文件),永不相等;没有回退,写入方存的缓存读取方
        // 就够不着,于是每轮都联网重下工具链。实测:仓库里有 695MB 的 elan 缓存,而
        // engineering job 从来没命中过。
        // 用 YAML 解析而非正则:step 里的注释会打断任何「key 紧跟 restore-keys」的文本假设。
        var elanRestores = Jobs(workflow).Children.Values
            .OfType<YamlMappingNode>()
            .Where(job => job.Children.ContainsKey(new YamlScalarNode("steps")))
            .SelectMany(job => ((YamlSequenceNode)job.Children[new YamlScalarNode("steps")])
                .Children.OfType<YamlMappingNode>())
            .Where(step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                && uses is YamlScalarNode { Value: not null } u
                && u.Value.StartsWith("actions/cache/restore@", StringComparison.Ordinal))
            .Where(step => step.Children.TryGetValue(new YamlScalarNode("with"), out var with)
                && with is YamlMappingNode w
                && w.Children.TryGetValue(new YamlScalarNode("path"), out var path)
                && path is YamlScalarNode { Value: "~/.elan" })
            .Select(step => (YamlMappingNode)step.Children[new YamlScalarNode("with")])
            .ToArray();

        Assert.Equal(2, elanRestores.Length);
        Assert.All(
            elanRestores,
            with => Assert.True(
                with.Children.ContainsKey(new YamlScalarNode("restore-keys")),
                "an ~/.elan restore without restore-keys can never reach the cache the other job wrote"));

        // 用 YAML 解析而非正则:步骤上方的注释会把「name 紧跟 if」的文本假设打断。
        var leanInspect = Assert.IsType<YamlMappingNode>(
            Jobs(workflow).Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(
            leanInspect.Children[new YamlScalarNode("steps")]);
        var save = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            node => node.Children.TryGetValue(new YamlScalarNode("name"), out var name)
                && name is YamlScalarNode { Value: not null } scalar
                && scalar.Value.StartsWith("Save elan toolchains", StringComparison.Ordinal));
        var condition = Assert.IsType<YamlScalarNode>(
            save.Children[new YamlScalarNode("if")]).Value ?? string.Empty;
        Assert.DoesNotContain("success()", condition, StringComparison.Ordinal);
        Assert.Contains("always()", condition, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanToolchainInstallerHonorsAttemptsAndGithubPath()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        var installer = Path.Combine(root, "tools", "scripts", "workflow", "install-lean-toolchain.sh");
        using var fixture = new TemporaryDirectory();
        var home = Path.Combine(fixture.Path, "home");
        var elanBin = Path.Combine(home, ".elan", "bin");
        var stubBin = Path.Combine(fixture.Path, "bin");
        var attempts = Path.Combine(fixture.Path, "attempts.log");
        var githubPath = Path.Combine(fixture.Path, "github-path");
        var toolchain = Path.Combine(fixture.Path, "lean-toolchain");
        Directory.CreateDirectory(elanBin);
        Directory.CreateDirectory(stubBin);
        File.WriteAllText(toolchain, "leanprover/lean4:v4.24.0\n");
        File.WriteAllText(
            Path.Combine(elanBin, "elan"),
            "#!/usr/bin/env bash\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == list ]]; then exit 0; fi\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == install ]]; then printf 'attempt\\n' >> \"$ATTEMPTS_LOG\"; exit 42; fi\n"
                + "exit 0\n");
        File.WriteAllText(Path.Combine(stubBin, "sleep"), "#!/usr/bin/env bash\nexit 0\n");
        File.SetUnixFileMode(
            Path.Combine(elanBin, "elan"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.SetUnixFileMode(
            Path.Combine(stubBin, "sleep"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "env",
            [
                $"HOME={home}",
                $"PATH={stubBin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"ATTEMPTS_LOG={attempts}",
                "/bin/bash",
                installer,
                toolchain,
                "--attempts",
                "2",
                "--github-path",
                githubPath,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(2, File.ReadAllLines(attempts).Length);
        Assert.Equal($"{elanBin}\n", File.ReadAllText(githubPath));
    }

    [Fact]
    public void BaselineAdmissionNeedsExactlyLeanInspect()
    {
        var workflow = AdmissionWorkflow();
        Assert.True(BaselineNeedsExactlyLeanInspect(workflow));
        var tampered = workflow.Replace("    needs: lean-inspect\n    runs-on: ubuntu-latest\n    timeout-minutes: 20",
            "    needs: [lean-inspect, some-other-job]\n    runs-on: ubuntu-latest\n    timeout-minutes: 20", StringComparison.Ordinal);
        Assert.False(BaselineNeedsExactlyLeanInspect(tampered));
    }

    // 历史方法名保留,避免删除或改名既有测试;契约已改为 merge result 的 dev 父提交。
    [Fact]
    public void DevBaselineIsTheForkPointNotTheMovingDevTip()
    {
        var workflow = AdmissionWorkflow();
        var resolve = BaselineResolutionScript(workflow);

        Assert.Contains("sha=\"$(git -C candidate rev-parse HEAD^1)\"", resolve, StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", resolve, StringComparison.Ordinal);
    }

    [Fact]
    public void AllJobsCheckoutMergeResultAndKeepPushFallback()
    {
        const string expectedRef = "${{ github.event_name == 'pull_request_target' && format('refs/pull/{0}/merge', github.event.pull_request.number) || github.sha }}";
        var workflow = SharedAdmissionWorkflow;

        foreach (var jobName in new[] { "candidate-engineering", "lean-inspect", "baseline-admission" })
        {
            var checkout = Assert.Single(
                JobSteps(workflow, jobName),
                step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                    && uses is YamlScalarNode { Value: "actions/checkout@v4" });
            var with = Assert.IsType<YamlMappingNode>(checkout.Children[new YamlScalarNode("with")]);
            var checkoutRef = Assert.IsType<YamlScalarNode>(with.Children[new YamlScalarNode("ref")]).Value;
            Assert.Equal(expectedRef, checkoutRef);
        }
    }

    [Fact]
    public void CandidateEngineeringInstallsPinnedSdkBeforeEveryDotnetCommand()
    {
        var steps = JobSteps(SharedAdmissionWorkflow, "candidate-engineering");
        var sdk = Assert.Single(
            steps.Select(static (step, index) => (Step: step, Index: index)),
            candidate => candidate.Step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                && uses is YamlScalarNode { Value: not null } scalar
                && scalar.Value.StartsWith("actions/setup-dotnet@", StringComparison.Ordinal));

        Assert.Equal(
            "actions/setup-dotnet@v4",
            Assert.IsType<YamlScalarNode>(sdk.Step.Children[new YamlScalarNode("uses")]).Value);
        var inputs = Assert.IsType<YamlMappingNode>(
            sdk.Step.Children[new YamlScalarNode("with")]);
        Assert.Equal(
            "candidate/global.json",
            Assert.IsType<YamlScalarNode>(
                inputs.Children[new YamlScalarNode("global-json-file")]).Value);
        Assert.False(
            sdk.Step.Children.ContainsKey(new YamlScalarNode("if")),
            "the candidate-engineering SDK setup step must not be conditionally disabled");

        var dotnetStepIndices = steps
            .Select(static (step, index) => (Step: step, Index: index))
            .Where(candidate => candidate.Step.Children.TryGetValue(
                    new YamlScalarNode("run"),
                    out var run)
                && run is YamlScalarNode { Value: not null } scalar
                && ContainsDotnetInvocation(scalar.Value))
            .ToArray();

        Assert.NotEmpty(dotnetStepIndices);
        Assert.All(
            dotnetStepIndices,
            candidate => Assert.True(
                sdk.Index < candidate.Index,
                $"the pinned SDK setup must precede dotnet command step '{StepName(candidate.Step)}'"));
    }

    [Fact]
    public void PullRequestDeltaIsDevParentToCheckedMergeResult()
    {
        var workflow = SharedAdmissionWorkflow;
        var scope = Assert.Single(
            JobSteps(workflow, "candidate-engineering"),
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        var scopeScript = Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        var baselineScript = BaselineResolutionScript(workflow);

        Assert.Contains(
            "base_sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            scopeScript,
            StringComparison.Ordinal);
        Assert.Contains(
            "head_sha=\"$(git -C candidate rev-parse HEAD)\"",
            scopeScript,
            StringComparison.Ordinal);
        Assert.Contains("HEAD=\"$head_sha\" BASE=\"$base_sha\"", scopeScript, StringComparison.Ordinal);
        Assert.Contains(
            "git -C candidate diff --name-only -z --no-renames --diff-filter=ACDMRTUXB \"$base_sha\" \"$head_sha\" --",
            scopeScript,
            StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", scopeScript, StringComparison.Ordinal);
        Assert.Contains(
            "sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            baselineScript,
            StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base", baselineScript, StringComparison.Ordinal);
        Assert.DoesNotContain("HEAD^2", scopeScript, StringComparison.Ordinal);
        Assert.DoesNotContain("HEAD^2", baselineScript, StringComparison.Ordinal);
    }

    [Fact]
    public void PushFallbackBaseIsCheckedHeadFirstParent()
    {
        var baselineScript = BaselineResolutionScript(SharedAdmissionWorkflow);

        Assert.Contains(
            "sha=\"$(git -C candidate rev-parse HEAD^1)\"",
            baselineScript,
            StringComparison.Ordinal);
        Assert.Single(Regex.Matches(
            baselineScript,
            Regex.Escape("sha=\"$(git -C candidate rev-parse HEAD^1)\"")));
        Assert.DoesNotContain("github.event.before", baselineScript, StringComparison.Ordinal);
        Assert.DoesNotContain("$GITHUB_SHA^", baselineScript, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingMergeResultFailsClosedWithConflictMessage()
    {
        var workflow = SharedAdmissionWorkflow;

        foreach (var jobName in new[] { "candidate-engineering", "lean-inspect", "baseline-admission" })
        {
            var steps = JobSteps(workflow, jobName);
            var checkoutIndex = Array.FindIndex(
                steps,
                step => step.Children.TryGetValue(new YamlScalarNode("uses"), out var uses)
                    && uses is YamlScalarNode { Value: "actions/checkout@v4" });
            Assert.True(checkoutIndex >= 0 && checkoutIndex + 2 < steps.Length);

            var checkout = steps[checkoutIndex];
            Assert.Equal("checkout-merge", Assert.IsType<YamlScalarNode>(
                checkout.Children[new YamlScalarNode("id")]).Value);
            Assert.Equal("${{ github.event_name == 'pull_request_target' }}", Assert.IsType<YamlScalarNode>(
                checkout.Children[new YamlScalarNode("continue-on-error")]).Value);

            Assert.Equal("Strip checkout remote state", StepName(steps[checkoutIndex + 1]));
            var failure = steps[checkoutIndex + 2];
            Assert.Equal("Fail closed when merge result is unavailable", StepName(failure));
            var condition = Assert.IsType<YamlScalarNode>(
                failure.Children[new YamlScalarNode("if")]).Value ?? string.Empty;
            var script = Assert.IsType<YamlScalarNode>(
                failure.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
            Assert.Contains("always()", condition, StringComparison.Ordinal);
            Assert.Contains("steps.checkout-merge.outcome != 'success'", condition, StringComparison.Ordinal);
            Assert.Contains("refs/pull/${{ github.event.pull_request.number }}/merge", script, StringComparison.Ordinal);
            Assert.Contains("conflicted pull requests have no merge result", script, StringComparison.Ordinal);
            Assert.Contains("admission fails closed", script, StringComparison.Ordinal);
            Assert.Contains("exit 1", script, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CandidateEngineeringUsesOneThreeStatePlannerWithABaseOwnedFullFloor()
    {
        var engineering = Job(AdmissionWorkflow(), "candidate-engineering");
        var steps = Assert.IsType<YamlSequenceNode>(
            engineering.Children[new YamlScalarNode("steps")]).Children
            .OfType<YamlMappingNode>()
            .ToArray();
        Assert.True(steps.Length > 4);
        Assert.Equal("Wait for the GitHub merge ref", StepName(steps[0]));
        Assert.Equal("Check out candidate", StepName(steps[1]));

        var scopeIndex = Array.FindIndex(
            steps,
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        Assert.True(scopeIndex > 0);
        var scope = steps[scopeIndex];
        Assert.Equal("scope", Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("id")]).Value);
        var scopeScript = Assert.IsType<YamlScalarNode>(
            scope.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        Assert.Contains("git -C candidate rev-parse HEAD^1", scopeScript, StringComparison.Ordinal);
        Assert.Contains("git -C candidate rev-parse HEAD", scopeScript, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools engineering-tests", scopeScript, StringComparison.Ordinal);
        Assert.Contains("MODE=plan", scopeScript, StringComparison.Ordinal);
        Assert.Contains("FULL=1", scopeScript, StringComparison.Ordinal);
        Assert.Contains("engineering-test-plan.json", scopeScript, StringComparison.Ordinal);
        Assert.Contains("base_full_required=false", scopeScript, StringComparison.Ordinal);
        Assert.Contains("git -C candidate diff --name-only -z", scopeScript, StringComparison.Ordinal);
        Assert.Contains("tools|tools/*|.github/workflows/ci.yml", scopeScript, StringComparison.Ordinal);
        Assert.Contains("run_required=$run_required", scopeScript, StringComparison.Ordinal);
        Assert.Contains("fallback_count=$fallback_count", scopeScript, StringComparison.Ordinal);
        Assert.Contains("ENGINEERING_TEST_PLAN_FALLBACK", scopeScript, StringComparison.Ordinal);
        Assert.DoesNotContain("ls-tree", scopeScript, StringComparison.Ordinal);
        Assert.DoesNotContain("StrataLint.EngineeringScope.csproj", scopeScript, StringComparison.Ordinal);

        var summary = steps[^1];
        Assert.Equal("Summarize candidate engineering scope", StepName(summary));
        Assert.Equal("always()", Assert.IsType<YamlScalarNode>(
            summary.Children[new YamlScalarNode("if")]).Value);
        var summaryScript = Assert.IsType<YamlScalarNode>(
            summary.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
        // 明细走日志、摘要只走计数:逐条路径不进 step output,因而不经 env 传给这一步。
        // 有界性本身由 WorkflowOutputBoundTests 判,这里只钉"摘要读的是计数"。
        Assert.Contains("$SCOPE_CHANGED_COUNT", summaryScript, StringComparison.Ordinal);
        Assert.Contains("$SCOPE_SELECTED_COUNT", summaryScript, StringComparison.Ordinal);
        Assert.Contains("SCOPE_FALLBACK_COUNT", summaryScript, StringComparison.Ordinal);
        Assert.Contains("$GITHUB_STEP_SUMMARY", summaryScript, StringComparison.Ordinal);

        Assert.Equal(
            "make -C candidate/tools dotnet",
            StepScript(steps, "Build candidate with warnings as errors"));
        var executeScript = StepScript(steps, "Run candidate golden and integration tests");
        Assert.Contains("if [[ \"$BASE_FULL_REQUIRED\" == \"true\" ]]", executeScript, StringComparison.Ordinal);
        Assert.Contains("dotnet test \"$project\"", executeScript, StringComparison.Ordinal);
        Assert.Contains("verify-trx --results-directory \"$assembly_results\"", executeScript, StringComparison.Ordinal);
        Assert.DoesNotContain("ENGINEERING_TEST_TARGET", executeScript, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools engineering-tests MODE=execute", executeScript, StringComparison.Ordinal);
        Assert.Equal(
            "make -C candidate/tools selftest",
            StepScript(steps, "Run candidate selftest twice and compare bytes"));

        Assert.All(
            steps[(scopeIndex + 1)..^1],
            step => Assert.Contains(
                "steps.scope.outputs.run_required == 'true'",
                Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("if")]).Value,
                StringComparison.Ordinal));
    }

    [Fact]
    public void SelectedExecuteMissingPlannedIdentityFallsBackToUnfilteredFullRun()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "candidate");
        var project = Path.Combine(repository, "tools", "tests", "Probe", "Probe.csproj");
        Directory.CreateDirectory(Path.GetDirectoryName(project)!);
        File.WriteAllText(
            project,
            """
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><RestorePackagesWithLockFile>false</RestorePackagesWithLockFile></PropertyGroup>
              <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText(
            Path.Combine(Path.GetDirectoryName(project)!, "Probe.cs"),
            "using Xunit; public sealed class ProductionBoundaryProbe { [Fact] public void Runs() { } }\n");
        File.WriteAllText(
            Path.Combine(repository, "tools", "StrataLint.sln"),
            """
            Microsoft Visual Studio Solution File, Format Version 12.00
            # Visual Studio Version 17
            Project("{FAE04EC0-301F-11D3-BF4B-00C04F79EFBC}") = "Probe", "tests/Probe/Probe.csproj", "{BD700716-FC67-411D-B4E4-5F8C0A552E7B}"
            EndProject
            Global
                GlobalSection(SolutionConfigurationPlatforms) = preSolution
                    Release|Any CPU = Release|Any CPU
                EndGlobalSection
                GlobalSection(ProjectConfigurationPlatforms) = postSolution
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.ActiveCfg = Release|Any CPU
                    {BD700716-FC67-411D-B4E4-5F8C0A552E7B}.Release|Any CPU.Build.0 = Release|Any CPU
                EndGlobalSection
            EndGlobal
            """);
        Git(repository, "init", "--quiet");
        Git(repository, "config", "user.email", "engineering-boundary@example.invalid");
        Git(repository, "config", "user.name", "engineering-boundary");
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "-m", "base");
        File.AppendAllText(Path.Combine(Path.GetDirectoryName(project)!, "Probe.cs"), "// candidate\n");
        Git(repository, "add", ".");
        Git(repository, "commit", "--quiet", "-m", "candidate");
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var planFile = Path.Combine(fixture.Path, "plan.json");
        File.WriteAllText(planFile, System.Text.Json.JsonSerializer.Serialize(new
        {
            version = 1,
            head,
            @base,
            plan = new
            {
                kind = "selected",
                changed_paths = new[] { "Meta/Digestion/probe.json" },
                tests = new[]
                {
                    new
                    {
                        project_path = "tools/tests/Probe/Probe.csproj",
                        id = "ProductionBoundaryProbe.Runs",
                        reason = "unknown_input",
                        detail = "production boundary probe",
                    },
                    new
                    {
                        project_path = "tools/tests/Probe/Probe.csproj",
                        id = "ProductionBoundaryProbe.Missing",
                        reason = "unknown_input",
                        detail = "planned identity with no executed result",
                    },
                },
                reason = "production boundary probe",
            },
        }));

        var probeBuild = BoundedProcessRunner.Run(
            DotnetHost(root),
            ["build", project, "--configuration", "Release", "--nologo"],
            repository,
            TestBudgets.LongWorkflowProcessHangGuard,
            1024 * 1024);
        Assert.True(
            probeBuild.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(probeBuild.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(probeBuild.StandardError));

        var result = RunEngineeringScope(root, repository, planFile, head, @base);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        var error = System.Text.Encoding.UTF8.GetString(result.StandardError);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            "ENGINEERING_TEST_EVIDENCE_FAILED TRX is missing planned tests: Probe::ProductionBoundaryProbe.Missing",
            error,
            StringComparison.Ordinal);
        Assert.Contains("filter=null evidence=trx executed=1", output, StringComparison.Ordinal);
    }

    [Fact]
    public void TruncatedPlannerArtifactInRealWorkflowFallsBackToProductionUnfilteredInvocation()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "candidate");
        Directory.CreateDirectory(Path.Combine(repository, "tools"));
        Git(repository, "init", "--quiet");
        Git(repository, "config", "user.email", "engineering-fallback@example.invalid");
        Git(repository, "config", "user.name", "engineering-fallback");
        File.WriteAllText(Path.Combine(repository, "tools", "planner.txt"), "base\n");
        Git(repository, "add", "tools/planner.txt");
        Git(repository, "commit", "--quiet", "-m", "base");
        File.AppendAllText(Path.Combine(repository, "tools", "planner.txt"), "candidate\n");
        Git(repository, "add", "tools/planner.txt");
        Git(repository, "commit", "--quiet", "-m", "candidate");
        var head = GitText(repository, "rev-parse", "HEAD");
        var @base = GitText(repository, "rev-parse", "HEAD^1");
        var bin = Path.Combine(fixture.Path, "bin");
        var calls = Path.Combine(fixture.Path, "dotnet.calls");
        var outputs = Path.Combine(fixture.Path, "scope.outputs");
        var runnerTemp = Path.Combine(fixture.Path, "runner-temp");
        var planFile = Path.Combine(runnerTemp, "engineering-test-plan.json");
        Directory.CreateDirectory(bin);
        Directory.CreateDirectory(runnerTemp);
        WriteExecutable(
            Path.Combine(bin, "make"),
            "#!/usr/bin/env bash\n"
                + "plan=''\n"
                + "for argument in \"$@\"; do case \"$argument\" in PLAN_FILE=*) plan=\"${argument#PLAN_FILE=}\" ;; esac; done\n"
                + "printf '%s' '{\"version\":1,\"head\":' > \"$plan\"\n");
        WriteExecutable(
            Path.Combine(bin, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" > \"$ENGINEERING_CALLS\"\nexit 23\n");

        var scope = Assert.Single(
            JobSteps(AdmissionWorkflow(), "candidate-engineering"),
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        var scopeScript = Assert.IsType<YamlScalarNode>(scope.Children[new YamlScalarNode("run")]).Value!;
        var scopeResult = BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                "GITHUB_EVENT_NAME=pull_request_target",
                $"RUNNER_TEMP={runnerTemp}",
                $"GITHUB_OUTPUT={outputs}",
                "/bin/bash",
                "-c",
                scopeScript,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, scopeResult.ExitCode);
        Assert.Equal(20, new FileInfo(planFile).Length);
        var scopeOutputs = ReadTemporaryText(outputs);
        Assert.Contains("state=full", scopeOutputs, StringComparison.Ordinal);
        Assert.Contains("base_full_required=true", scopeOutputs, StringComparison.Ordinal);
        Assert.Contains("run_required=true", scopeOutputs, StringComparison.Ordinal);
        Assert.Contains("fallback_count=1", scopeOutputs, StringComparison.Ordinal);

        var result = RunEngineeringScope(
            root,
            repository,
            planFile,
            head,
            @base,
            $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
            $"ENGINEERING_CALLS={calls}");

        Assert.Equal(23, result.ExitCode);
        Assert.Contains(
            "ENGINEERING_TEST_PLAN_FALLBACK",
            System.Text.Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        var invocation = ReadTemporaryText(calls);
        Assert.Contains("test tools/StrataLint.sln", invocation, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", invocation, StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightEngineeringScopeUsesCompleteCandidateDeltaAcrossMultipleCommits()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        var preflight = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/preflight.sh"));
        Assert.Contains("ENGINEERING_HEAD=\"$CANDIDATE_SHA\"", preflight, StringComparison.Ordinal);
        Assert.Contains("ENGINEERING_BASE=\"$BASE_SHA\"", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("ENGINEERING_BASE=\"$(git rev-parse HEAD^1)\"", preflight, StringComparison.Ordinal);

        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "candidate");
        Directory.CreateDirectory(repository);
        Git(repository, "init", "--quiet");
        Git(repository, "config", "user.email", "engineering-complete-delta@example.invalid");
        Git(repository, "config", "user.name", "engineering-complete-delta");
        File.WriteAllText(Path.Combine(repository, "README.md"), "base\n");
        Git(repository, "add", "README.md");
        Git(repository, "commit", "--quiet", "-m", "base");
        var @base = GitText(repository, "rev-parse", "HEAD");
        Directory.CreateDirectory(Path.Combine(repository, "Blueprint"));
        File.WriteAllText(Path.Combine(repository, "Blueprint", "probe.scribe.cs"), "blueprint input\n");
        Git(repository, "add", "Blueprint/probe.scribe.cs");
        Git(repository, "commit", "--quiet", "-m", "blueprint change");
        Directory.CreateDirectory(Path.Combine(repository, "docs"));
        File.WriteAllText(Path.Combine(repository, "docs", "note.md"), "docs only\n");
        Git(repository, "add", "docs/note.md");
        Git(repository, "commit", "--quiet", "-m", "docs only");
        var head = GitText(repository, "rev-parse", "HEAD");
        var planFile = Path.Combine(fixture.Path, "plan.json");

        var result = RunEngineeringScopeMode(root, repository, planFile, head, @base, "plan", "FULL=1");

        Assert.Equal(0, result.ExitCode);
        using var artifact = System.Text.Json.JsonDocument.Parse(ReadTemporaryText(planFile));
        var changedPaths = artifact.RootElement.GetProperty("plan").GetProperty("changed_paths")
            .EnumerateArray()
            .Select(static path => path.GetString())
            .ToArray();
        Assert.Contains("Blueprint/probe.scribe.cs", changedPaths);
        Assert.Contains("docs/note.md", changedPaths);
    }

    [Fact]
    public void PlannerNoneAndSolutionWithoutTestMembersStillExecutesEveryBaseOwnedRequiredAssembly()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var candidate = Path.Combine(fixture.Path, "candidate");
        var bin = Path.Combine(fixture.Path, "bin");
        var runnerTemp = Path.Combine(fixture.Path, "runner-temp");
        var outputs = Path.Combine(fixture.Path, "scope.outputs");
        Directory.CreateDirectory(Path.Combine(candidate, "tools"));
        Directory.CreateDirectory(bin);
        Directory.CreateDirectory(runnerTemp);
        var marker = Path.Combine(fixture.Path, "floor.executed");
        WriteFloorProject(candidate, "StrataLint.Tests", "StrataLintTestsFloorProbe");
        WriteFloorProject(candidate, "StrataLint.Scribe.Tests", "StrataLintScribeTestsFloorProbe");
        WriteFloorProject(candidate, "StrataLint.ArchitectureTests", "StrataLintArchitectureTestsFloorProbe");
        WriteEngineeringScopeVerifierStub(candidate);
        File.WriteAllText(
            Path.Combine(candidate, "tools", "StrataLint.sln"),
            "Microsoft Visual Studio Solution File, Format Version 12.00\n# Visual Studio Version 17\nGlobal\nEndGlobal\n");
        Git(candidate, "init", "--quiet");
        Git(candidate, "config", "user.email", "engineering-floor@example.invalid");
        Git(candidate, "config", "user.name", "engineering-floor");
        File.WriteAllText(Path.Combine(candidate, "tools", "planner.txt"), "base\n");
        Git(candidate, "add", "tools/planner.txt");
        Git(candidate, "commit", "--quiet", "-m", "base");
        File.WriteAllText(Path.Combine(candidate, "tools", "planner.txt"), "candidate\n");
        Git(candidate, "add", "tools/planner.txt");
        Git(candidate, "commit", "--quiet", "-m", "candidate");
        WriteExecutable(
            Path.Combine(bin, "make"),
            """
            #!/usr/bin/env bash
            plan=""
            head=""
            base=""
            for argument in "$@"; do
              case "$argument" in
                PLAN_FILE=*) plan="${argument#PLAN_FILE=}" ;;
                HEAD=*) head="${argument#HEAD=}" ;;
                BASE=*) base="${argument#BASE=}" ;;
              esac
            done
            [[ -n "$plan" && -n "$head" && -n "$base" ]] || exit 24
            printf '{"version":1,"head":"%s","base":"%s","plan":{"kind":"none","changed_paths":["tools/planner.txt"],"tests":[],"reason":"mutated planner always returns none"}}\n' "$head" "$base" > "$plan"
            """);

        var workflow = AdmissionWorkflow();
        var scope = Assert.Single(
            JobSteps(workflow, "candidate-engineering"),
            step => step.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "scope" });
        var scopeScript = Assert.IsType<YamlScalarNode>(scope.Children[new YamlScalarNode("run")]).Value!;
        var scopeResult = BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                "GITHUB_EVENT_NAME=pull_request_target",
                $"RUNNER_TEMP={runnerTemp}",
                $"GITHUB_OUTPUT={outputs}",
                "/bin/bash",
                "-c",
                scopeScript,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, scopeResult.ExitCode);
        var scopeOutputs = ReadTemporaryText(outputs);
        Assert.Contains("state=none", scopeOutputs, StringComparison.Ordinal);
        Assert.Contains("base_full_required=true", scopeOutputs, StringComparison.Ordinal);
        Assert.Contains("run_required=true", scopeOutputs, StringComparison.Ordinal);

        var executeScript = StepScript(JobSteps(workflow, "candidate-engineering"), "Run candidate golden and integration tests");
        Assert.DoesNotContain("--filter", executeScript, StringComparison.Ordinal);
        var execute = BoundedProcessRunner.Run(
            "env",
            [
                "BASE_FULL_REQUIRED=true",
                "PLAN_STATE=none",
                $"RUNNER_TEMP={runnerTemp}",
                $"ENGINEERING_FLOOR_MARKER={marker}",
                $"ENGINEERING_HEAD={GitText(candidate, "rev-parse", "HEAD")}",
                $"ENGINEERING_BASE={GitText(candidate, "rev-parse", "HEAD^1")}",
                "/bin/bash",
                "-c",
                executeScript,
            ],
            fixture.Path,
            TestBudgets.ReportSupervisorHangGuard,
            2 * 1024 * 1024);

        var executeOutput = System.Text.Encoding.UTF8.GetString(execute.StandardOutput)
            + System.Text.Encoding.UTF8.GetString(execute.StandardError);
        Assert.True(execute.ExitCode == 0, executeOutput);
        foreach (var assembly in new[] { "StrataLint.Tests", "StrataLint.Scribe.Tests", "StrataLint.ArchitectureTests" })
        {
            Assert.Contains($"assembly={assembly}", executeOutput, StringComparison.Ordinal);
        }
        Assert.Equal(
            new[] { "StrataLint.ArchitectureTests", "StrataLint.Scribe.Tests", "StrataLint.Tests" },
            File.ReadAllLines(marker).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void RunsCompleteMathematicalChecksAfterProducingLiveReport()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var namedSteps = steps.Children.OfType<YamlMappingNode>()
            .Select(static step => new
            {
                Node = step,
                Name = Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value,
            })
            .ToArray();
        var reportIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Produce source-bound canonical Lean reports");
        var reconciliationIndex = Array.FindIndex(namedSteps, static step =>
            step.Name == "Run complete mathematical content checks");
        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "mathematical checks must run after report production");

        var reconciliation = namedSteps[reconciliationIndex].Node;
        var run = Assert.IsType<YamlScalarNode>(reconciliation.Children[new YamlScalarNode("run")]).Value!;
        Assert.Contains("tools/scripts/workflow/scribe-content-checks.sh", run, StringComparison.Ordinal);
        Assert.Contains("steps.base.outputs.sha", run, StringComparison.Ordinal);
        Assert.Contains("\"$report\" \"$scribe\" \"$base\"", run, StringComparison.Ordinal);
        Assert.Contains(".judge-binaries/scribe/StrataLint.Scribe.dll", run, StringComparison.Ordinal);
        Assert.DoesNotContain("--changes-file", run, StringComparison.Ordinal);
        Assert.DoesNotContain("--producer-paths-file", run, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet test", run, StringComparison.Ordinal);
        Assert.DoesNotContain("tools/tests", run, StringComparison.Ordinal);
    }

    [Fact]
    public void JudgeBinaryCacheIsSharedByEngineeringAndBothContentJobs()
    {
        var workflow = AdmissionWorkflow();
        var cacheKeyLines = workflow.Split('\n')
            .Where(static line => line.TrimStart().StartsWith(
                "key: stratalint-judge-binaries-v2-",
                StringComparison.Ordinal))
            .Select(static line => line.Trim())
            .Distinct(StringComparer.Ordinal)
            .ToArray();

        Assert.Single(cacheKeyLines);
        Assert.Equal(2, Regex.Matches(workflow, "- name: Restore judge binaries").Count);
        Assert.Equal(3, Regex.Matches(
            workflow,
            "- name: Resolve judge binary content address before build outputs exist").Count);
        Assert.Equal(3, Regex.Matches(workflow, "hashFiles\\('candidate/tools/\\*\\*'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/Blueprint/\\*\\*/\\*.scribe.cs'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/Directory.\\*'").Count);
        Assert.Equal(3, Regex.Matches(workflow, "'candidate/global.json'").Count);

        var engineering = JobText(workflow, "candidate-engineering", "lean-inspect");
        var leanInspect = JobText(workflow, "lean-inspect", "baseline-admission");
        var admission = workflow[workflow.IndexOf("  baseline-admission:", StringComparison.Ordinal)..];
        Assert.Contains("dotnet publish", engineering, StringComparison.Ordinal);
        Assert.Contains("github.event_name == 'push'", engineering, StringComparison.Ordinal);
        Assert.Contains("github.ref == 'refs/heads/dev'", engineering, StringComparison.Ordinal);
        Assert.Contains("actions/cache/save@v4", engineering, StringComparison.Ordinal);
        Assert.Contains("actions/cache/restore@v4", leanInspect, StringComparison.Ordinal);
        Assert.Contains("dotnet build candidate/tools/StrataLint.Scribe/StrataLint.Scribe.csproj", leanInspect, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet test", leanInspect, StringComparison.Ordinal);
        Assert.Contains("actions/cache/restore@v4", admission, StringComparison.Ordinal);
        Assert.Contains("--judge-dll", admission, StringComparison.Ordinal);
    }

}

[CollectionDefinition("Engineering execution boundary", DisableParallelization = true)]
public sealed class EngineeringExecutionBoundaryCollectionDefinition;
