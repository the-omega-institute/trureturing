using System.Text.Json.Nodes;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    private const string InspectorTestPath = "tools/lean-inspector/LeanInformationAudit/Tests/RegistrationGates/ConservativeCorpus.lean";
    private static readonly string[] InspectorTestRequirements =
        ["architecture", "current", "delta-data", "filemap", "scribe", "test-cache", "test-cli"];

    [Theory]
    [InlineData("pr")]
    [InlineData("push")]
    public void InspectorTestChangesKeepReportAndOnlyRegisteredEngineeringConsumers(string mode)
    {
        var plan = InspectorPlan(InspectorTestPath, mode);
        Assert.Equal(InspectorTestRequirements, Strings(plan["declared_require"]!));
        Assert.Equal(new[] { "StrataLint.ArchitectureTests", "StrataLint.Cache.Tests", "StrataLint.Tests" },
            Strings(plan["execution"]!["projects"]!).Where(path => path.StartsWith("tools/tests/", StringComparison.Ordinal))
                .Select(Path.GetFileNameWithoutExtension));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
        Assert.DoesNotContain("delta", Strings(plan["resources"]!));
        Assert.DoesNotContain(Strings(plan["execution"]!["checks"]!), CommonExecutionEvidence.EngineeringCheckIds.Contains);
        Assert.Contains("SL-008", Strings(plan["execution"]!["checks"]!));
        Assert.Contains("scribe-projections", Strings(plan["execution"]!["checks"]!));
        Assert.Equal(new[] { "lean-report", "scribe", "filemap", "check-current" }, Strings(plan["execution"]!["steps"]!));
        Assert.Equal(mode == "pr" ? "required" : "not-applicable", plan["stages"]!["delta"]!["status"]!.GetValue<string>());
    }

    [Theory]
    [InlineData("tools/lean-inspector/Inspector.lean")]
    [InlineData("tools/lean-inspector/lakefile.lean")]
    [InlineData("tools/lean-inspector/Census/project.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Registry.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Census/AdmissionResourceProbe.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Projection/AdmissionResourceProbe.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/ReadoutProvenance/AdmissionResourceProbe.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAudit/Registry/AdmissionResourceProbe.lean")]
    [InlineData("tools/lean-inspector/LeanInformationAuditAnalysis/Tests/AdmissionResourceProbe.lean")]
    public void InspectorProductionChangesRetainFullEngineering(string path)
    {
        var plan = InspectorPlan(path, "pr");
        Assert.Equal(new[] { "current", "delta", "engineering", "filemap", "lean-report", "scribe" },
            Strings(plan["declared_require"]!));
        foreach (var check in CommonExecutionEvidence.EngineeringCheckIds)
            Assert.Contains(check, Strings(plan["execution"]!["checks"]!));
        Assert.Contains("lean-report", Strings(plan["execution"]!["steps"]!));
    }

    [Theory]
    [InlineData("pr")]
    [InlineData("push")]
    public void InspectorTestChangesCannotHideProductionRequirements(string mode)
    {
        const string production = "tools/lean-inspector/LeanInformationAudit/Registry.lean";
        var alone = InspectorPlan(production, mode);
        var mixed = InspectorPlan(InspectorTestPath, mode, companion: production);
        foreach (var field in new[] { "resources", "tools", "cache_layers" })
            Assert.Empty(Strings(alone[field]!).Except(Strings(mixed[field]!)));
        foreach (var field in new[] { "checks", "steps", "projects" })
            Assert.Empty(Strings(alone["execution"]![field]!).Except(Strings(mixed["execution"]![field]!)));
        Assert.Contains("engineering", Strings(mixed["resources"]!));
    }

    [Theory]
    [InlineData("pr")]
    [InlineData("push")]
    public void InspectorTestDeletionUsesHistoricalRequirementsDespiteCandidateWaiver(string mode)
    {
        var plan = InspectorPlan(InspectorTestPath, mode, removed: true);
        var removed = plan["paths"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == InspectorTestPath)!;
        Assert.Equal(InspectorTestRequirements, Strings(removed["require"]!));
        // The candidate FILEMAP edit is independently broad. Inspect the removed
        // endpoint itself so that companion cannot mask a historical-scope leak.
        Assert.Contains("architecture", Strings(plan["declared_require"]!));
        Assert.Contains("test-cache", Strings(plan["declared_require"]!));
    }

    private JsonNode InspectorPlan(string path, string mode, string companion = "", bool removed = false)
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
            paths = list(filter(None, sys.argv[5:7]))
            for path in paths:
                target = root / path
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.is_file():
                    target.write_text('-- registered fixture\n')
            git('add', '.')
            git('commit', '--allow-empty', '-qm', 'existing inspector inputs')
            base = git('rev-parse', 'HEAD')
            if sys.argv[8] == 'true':
                (root / paths[0]).unlink()
                mapping = root / ci_plan.FILEMAP
                manifest = ci_plan.load_filemap(mapping.read_bytes(), lambda path: (root / path).read_bytes())
                row, = [row for row in manifest['files'] if ci_plan.glob(row['pattern']).fullmatch(paths[0])]
                marker = 'pattern = ' + json.dumps(row['pattern'])
                lines = mapping.read_text().splitlines(keepends=True)
                for i, line in enumerate(lines):
                    if marker in line:
                        before, requirements = line.split('require = [', 1)
                        lines[i] = before + 'require = []' + requirements.split(']', 1)[1]
                mapping.write_text(''.join(lines))
            else:
                for path in paths:
                    target = root / path
                    target.write_bytes(target.read_bytes() + b'\n-- changed fixture\n')
            git('add', '-A')
            git('commit', '-qm', 'candidate inspector change')
            head = git('rev-parse', 'HEAD')
            merge = git('commit-tree', git('rev-parse', 'HEAD^{tree}'), '-p', base, '-p', head, '-m', 'candidate')
            git('checkout', '--detach', '-q', merge)
            changes = root / 'build/ci/changes.json'
            scope = ci_plan.push_paths(root, merge, base, merge) if sys.argv[7] == 'push' else ci_plan.pr_paths(root, merge, base, head)
            ci_plan.write(changes, scope)
            print(json.dumps(ci_plan.make_plan(root, merge, changes)))
            """, basis.Path, basis.Commit, path, companion, mode, removed ? "true" : "false");
        Assert.True(result.Exit == 0, result.Text);
        return JsonNode.Parse(result.Text)!;
    }
}
