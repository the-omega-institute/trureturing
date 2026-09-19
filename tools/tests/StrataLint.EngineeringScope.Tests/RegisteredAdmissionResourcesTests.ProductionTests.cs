using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string BackfillProductionPath = "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryLoader.cs";
    private static readonly string[] ProductionCommonTests =
        ["StrataLint.ArchitectureTests", "StrataLint.Policy.Tests", "StrataLint.Repository.Tests", "StrataLint.Tests"];

    public static IEnumerable<object[]> ProductionSourceCases()
    {
        (string Path, string Owner)[] sources =
        [
            ("tools/StrataLint.Cli/AdmissionResourceProbe.cs", "StrataLint.Tests"),
            (BackfillProductionPath, "StrataLint.Engine.Tests"),
            ("tools/StrataLint.EngineeringScope/AdmissionResourceProbe.cs", "StrataLint.EngineeringScope.Tests"),
            ("tools/StrataLint.Lean/AdmissionResourceProbe.cs", "StrataLint.Lean.Tests"),
            ("tools/StrataLint.Scribe.Documents/AdmissionResourceProbe.cs", "StrataLint.Scribe.Documents.Tests"),
            ("tools/StrataLint.Scribe/AdmissionResourceProbe.cs", "StrataLint.Scribe.Tests"),
            ("tools/Trureturing.Truth/AdmissionResourceProbe.cs", "Trureturing.Truth.Tests"),
            ("tools/scripts/report/JudgeSeedTask.cs", "JudgeSeedTask.Tests"),
        ];
        foreach (var (path, owner) in sources)
            foreach (var mode in new[] { "pr", "push" })
                yield return [path, owner, mode];
    }

    [Theory]
    [MemberData(nameof(ProductionSourceCases))]
    public void ProductionSourceChangesSelectCompleteOwnedAndRegisteredConsumerProjects(string path, string owner, string mode)
    {
        var plan = ProductionPlan(mode, [path]);
        AssertProductionSelection(plan, mode, ExpectedProductionTests(owner));
    }

    [Theory]
    [InlineData("pr")]
    [InlineData("push")]
    public void ProductionBackfillRepairSelectsFiveProjectsWithoutReferenceExpansion(string mode)
    {
        var plan = ProductionPlan(mode,
        [
            BackfillProductionPath,
            "tools/tests/StrataLint.Tests/Rules/Backfill/BackfillInventoryLoaderTests.DirectoryProjection.cs",
            "tools/tests/StrataLint.Tests/Rules/Backfill/Sl016InheritedDuplicateTests.cs",
        ]);
        Assert.Equal(3, plan["paths"]!.AsArray().Count);
        AssertProductionSelection(plan, mode, ExpectedProductionTests("StrataLint.Engine.Tests"));
        // EngineeringScope and Lean reference Engine, but that build relationship
        // does not select their test projects for this registered Backfill change.
        foreach (var name in new[] { "StrataLint.EngineeringScope.Tests", "StrataLint.Lean.Tests", "StrataLint.Cache.Tests", "JudgeSeedTask.Tests" })
            Assert.DoesNotContain(TestProject(name), Strings(plan["execution"]!["projects"]!));
    }

    [Theory]
    [InlineData("pr")]
    [InlineData("push")]
    public void ProductionSourcesUnionTheirExplicitConsumers(string mode)
    {
        var plan = ProductionPlan(mode,
            [BackfillProductionPath, "tools/StrataLint.Lean/AdmissionResourceProbe.cs", RegisteredNoResourceContent]);
        AssertProductionSelection(plan, mode,
            ExpectedProductionTests("StrataLint.Engine.Tests").Append("StrataLint.Lean.Tests").Order(StringComparer.Ordinal));
        var noResource = plan["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == RegisteredNoResourceContent)!;
        Assert.Empty(Strings(noResource["require"]!));
    }

    [Theory]
    [MemberData(nameof(ProductionSourceCases))]
    public void ProductionSourceDeletionUsesBaselineRegistration(string path, string owner, string mode)
    {
        var before = ProductionPlan(mode, [path]);
        var removed = ProductionPlan(mode, [path], removed: true);
        var originalRow = before["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == path)!;
        var removedRow = removed["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == path)!;
        Assert.Equal(Strings(originalRow["require"]!), Strings(removedRow["require"]!));
        Assert.Contains("delta-judge", Strings(removedRow["require"]!));
        Assert.Contains("engineering-guards", Strings(removedRow["require"]!));
        // The candidate's FILEMAP change independently selects broad checks.
        // The removed endpoint must still retain the baseline source obligations.
        Assert.DoesNotContain("engineering", Strings(removedRow["require"]!));
        Assert.Contains(owner switch
        {
            "StrataLint.Tests" => "test-cli",
            "StrataLint.Engine.Tests" => "test-engine",
            "StrataLint.EngineeringScope.Tests" => "test-engineering-scope",
            "StrataLint.Lean.Tests" => "test-lean",
            "StrataLint.Scribe.Documents.Tests" => "test-scribe-documents",
            "StrataLint.Scribe.Tests" => "test-scribe",
            "Trureturing.Truth.Tests" => "test-truth",
            "JudgeSeedTask.Tests" => "test-judge-seed",
            _ => throw new ArgumentOutOfRangeException(nameof(owner)),
        }, Strings(removedRow["require"]!));
    }

    [Theory]
    [InlineData("tools/StrataLint.Cli/StrataLint.Cli.csproj")]
    [InlineData("tools/StrataLint.Engine/StrataLint.Engine.csproj")]
    [InlineData("tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj")]
    [InlineData("tools/StrataLint.Lean/StrataLint.Lean.csproj")]
    [InlineData("tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj")]
    [InlineData("tools/StrataLint.Scribe/StrataLint.Scribe.csproj")]
    [InlineData("tools/Trureturing.Truth/Trureturing.Truth.csproj")]
    [InlineData("tools/scripts/report/JudgeSeedTask.csproj")]
    [InlineData("tools/StrataLint.Engine/packages.lock.json")]
    [InlineData("tools/Trureturing.Truth/packages.lock.json")]
    [InlineData("tools/scripts/report/packages.lock.json")]
    [InlineData("tools/StrataLint.Scribe/Vendor/Katex/katex.min.js")]
    public void ProductionProjectConfigurationAndVendorKeepFullEngineering(string path)
    {
        var plan = ProductionPlan("pr", [BackfillProductionPath, path]);
        Assert.Contains("engineering", Strings(plan["resources"]!));
        Assert.Contains("delta", Strings(plan["resources"]!));
        foreach (var check in CommonExecutionEvidence.EngineeringCheckIds)
            Assert.Contains(check, Strings(plan["execution"]!["checks"]!));
        var registered = JsonNode.Parse(TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/engineering-projects.json")))!["projects"]!.AsArray();
        var expected = registered.Where(row => row!["ci"]!.GetValue<bool>()).Select(row => row!["path"]!.GetValue<string>()).Order(StringComparer.Ordinal);
        Assert.Equal(expected, Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal)));
    }

    [Theory]
    [InlineData("tools/StrataLint.Unregistered/AdmissionResourceProbe.cs")]
    [InlineData("tools/StrataLint.Unregistered/StrataLint.Unregistered.csproj")]
    [InlineData("tools/scripts/report/UnregisteredTask.cs")]
    public void ProductionUnknownProjectHasNoFullEngineeringFallback(string path)
    {
        var result = PlanResult(path, "");
        Assert.NotEqual(0, result.Exit);
        Assert.Contains("FILEMAP match count 0", result.Text, StringComparison.Ordinal);
    }

    private static IEnumerable<string> ExpectedProductionTests(string owner) =>
        ProductionCommonTests.Append(owner)
            .Concat(owner == "JudgeSeedTask.Tests" ? new[] { "StrataLint.Cache.Tests", "StrataLint.EngineeringScope.Tests" } : [])
            .Distinct().Order(StringComparer.Ordinal);

    private static string TestProject(string name) => $"tools/tests/{name}/{name}.csproj";

    private static void AssertProductionSelection(JsonNode plan, string mode, IEnumerable<string> expectedTests)
    {
        Assert.Equal(expectedTests.Select(TestProject), Strings(plan["execution"]!["projects"]!)
            .Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal)));
        Assert.Contains("engineering-guards", Strings(plan["resources"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.DoesNotContain("delta", Strings(plan["resources"]!));
        foreach (var check in CommonExecutionEvidence.EngineeringCheckIds)
            Assert.Contains(check, Strings(plan["execution"]!["checks"]!));
        Assert.Contains("scribe-projections", Strings(plan["execution"]!["checks"]!));
        Assert.Contains("lean-report", Strings(plan["execution"]!["steps"]!));
        Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
        if (mode == "pr")
        {
            Assert.Contains("delta-judge", Strings(plan["resources"]!));
            Assert.Contains("SL-008", Strings(plan["execution"]!["checks"]!));
            Assert.Contains("check-current", Strings(plan["execution"]!["steps"]!));
        }
        else
            Assert.DoesNotContain("delta-judge", Strings(plan["resources"]!));
    }

    private JsonNode ProductionPlan(string mode, string[] paths, bool removed = false)
    {
        using var temporary = new PlanningFixture();
        var result = Python(temporary.Path, """
            import json, pathlib, sys
            source, root = map(pathlib.Path, sys.argv[1:3])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            def git(*args):
                return ci_plan.git(root, '-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', *args).decode().strip()
            git('clone', '--quiet', '--no-hardlinks', sys.argv[3], str(root))
            assert git('rev-parse', 'HEAD') == sys.argv[4]
            paths = json.loads(sys.argv[5])
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.is_file():
                    target.write_text('// registered input\n')
            git('add', '.')
            git('commit', '--allow-empty', '-qm', 'existing production inputs')
            base = git('rev-parse', 'HEAD')
            if sys.argv[7] == 'true':
                (root / paths[0]).unlink()
                mapping = root / ci_plan.FILEMAP
                manifest = ci_plan.load_filemap(mapping.read_bytes(), lambda path: (root / path).read_bytes())
                row, = [row for row in manifest['files'] if ci_plan.glob(row['pattern']).fullmatch(paths[0])]
                marker = 'pattern = ' + json.dumps(row['pattern'])
                lines = mapping.read_text().splitlines(keepends=True)
                for i, line in enumerate(lines):
                    if marker in line:
                        prefix, requirements = line.split('require = [', 1)
                        lines[i] = prefix + 'require = []' + requirements.split(']', 1)[1]
                mapping.write_text(''.join(lines))
            else:
                for path in paths:
                    target = root / path
                    target.write_bytes(target.read_bytes() + b'\n')
            git('add', '-A')
            git('commit', '-qm', 'candidate production change')
            head = git('rev-parse', 'HEAD')
            merge = git('commit-tree', git('rev-parse', 'HEAD^{tree}'), '-p', base, '-p', head, '-m', 'candidate')
            git('checkout', '--detach', '-q', merge)
            changes = root / 'build/ci/changes.json'
            scope = ci_plan.push_paths(root, merge, base, merge) if sys.argv[6] == 'push' else ci_plan.pr_paths(root, merge, base, head)
            ci_plan.write(changes, scope)
            print(json.dumps(ci_plan.make_plan(root, merge, changes)))
            """, basis.Path, basis.Commit, JsonSerializer.Serialize(paths), mode, removed ? "true" : "false");
        Assert.True(result.Exit == 0, result.Text);
        return JsonNode.Parse(result.Text)!;
    }
}
