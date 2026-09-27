using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Fact]
    public void RegisteredResourceMaterialsSelectPolicyReadersAndCoverTheirExecutionInputs()
    {
        var result = Python(basis.Path, """
            import json, pathlib, sys
            source = pathlib.Path(sys.argv[1])
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import ci_plan
            read = lambda path: (source / path).read_bytes()
            manifest = ci_plan.load_filemap(read(ci_plan.FILEMAP), read)
            resources = {row['id']: row for row in manifest['resources']}
            materials = {path for row in resources.values() for path in [row['owner'], *row['materials']]}
            assert materials, 'resource owner/material declarations must not be empty'
            projects = {row['assembly']: row for row in
                ci_plan.strict_json_bytes(read('Meta/engineering-projects.json'))['projects']}
            queries = set(projects['StrataLint.ResourcePlanning.Tests']['execution_filemap_paths'])
            assert materials <= queries, ('unregistered FILEMAP queries', sorted(materials - queries))
            consumers = [projects[name] for name in [
                'StrataLint.RepositoryConfiguration.Tests',
                'StrataLint.RepositoryFileMap.Tests',
                'StrataLint.RepositoryTopology.Tests',
                'StrataLint.Scribe.Tests',
            ]]
            entries = [(ci_plan.glob(row['pattern']), row) for row in manifest['files']]
            for path in sorted(materials):
                matches = [row for pattern, row in entries if pattern.fullmatch(path)]
                assert len(matches) == 1, (path, 'resource material must have exactly one FILEMAP entry')
                selected = ci_plan.closure(resources, matches[0]['require'])
                execution = ci_plan.execution_selection(read, [resources[key] for key in selected], resources)
                for consumer in consumers:
                    assert consumer['ci'], (consumer['path'], 'must remain a complete CI test project')
                    assert consumer['path'] in execution['tests'], (path, consumer['path'], 'missing test selection')
                    assert any(ci_plan.glob(pattern).fullmatch(path)
                        for pattern in consumer['execution_inputs']), (path, consumer['path'], 'missing execution input')
                    assert not any(ci_plan.glob(pattern).fullmatch(path)
                        for pattern in consumer['execution_excludes']), (path, consumer['path'], 'excluded execution input')
            print(json.dumps({'resources': len(resources), 'materials': sorted(materials),
                'consumers': [row['path'] for row in consumers]}, sort_keys=True))
            """);

        Assert.True(result.Exit == 0, result.Text);
        output.WriteLine(result.Text);
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void ResourceOwnerModificationSelectsItsCompleteConsumers(string mode)
    {
        var plan = Plan("tools/StrataLint.Cli/Commands/FileMap/FileMapConformCommand.cs", "", mode, "M");
        Assert.Equal(WithWorktreeContract(new[]
        {
            "StrataLint.ArchitectureTests",
            "StrataLint.CliIntegration.Tests",
            "StrataLint.CoverBatch.Tests",
            "StrataLint.RepositoryConfiguration.Tests",
            "StrataLint.RepositoryContract.Tests",
            "StrataLint.RepositoryFileMap.Tests",
            "StrataLint.RepositoryTopology.Tests",
            "StrataLint.Scribe.Tests",
            "StrataLint.SourceAtomizer.Tests",
            "StrataLint.Tests",
            "StrataLint.TruthRelease.Tests",
        }.Select(name => $"tools/tests/{name}/{name}.csproj")), Strings(plan["execution"]!["tests"]!));
        Assert.DoesNotContain("engineering", Strings(plan["resources"]!));
    }

    [Theory]
    [InlineData("tools/StrataLint.Cli/Commands/FileMap/FileMapConformCommand.cs", "D")]
    [InlineData("tools/StrataLint.Cli/Commands/FileMap/FileMapConformCommand.cs", "R")]
    [InlineData("tools/scripts/worktree/lean-cache-run.sh", "D")]
    [InlineData("tools/scripts/worktree/lean-cache-run.sh", "R")]
    public void RemovedResourceOwnersAndMaterialsFailClosed(string path, string change)
    {
        foreach (var mode in new[] { "push", "pr" })
        {
            var result = PlanResult(path, "", mode, change);

            Assert.NotEqual(0, result.Exit);
            Assert.Contains($"missing resource owner/material {path}", result.Text, StringComparison.Ordinal);
        }
    }
}
