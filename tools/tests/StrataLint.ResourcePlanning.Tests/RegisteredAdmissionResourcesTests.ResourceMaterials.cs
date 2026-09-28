using Xunit;

namespace StrataLint.ResourcePlanning.Tests;

public sealed partial class RegisteredAdmissionResourcesTests
{
    [Fact]
    public void DeclaredTemplateNativeInputsCoverReportAndProducerContracts()
    {
        var result = Python(basis.Path, """
            import functools, importlib.util, json, pathlib, re, subprocess, sys
            source = pathlib.Path(sys.argv[1])
            spec = importlib.util.spec_from_file_location('selection', source / 'tools/scripts/report/lean-report-selection.py')
            selection = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(selection)
            inputs = selection.Selection(source)
            inputs.validate('lean-report')
            # Match the producer's effective working-tree inputs, including new
            # authored files before staging; ignored build outputs stay excluded.
            paths = subprocess.check_output(['git', '-C', str(source), 'ls-files',
                '--cached', '--others', '--exclude-standard', '-z']).decode().split('\0')
            projects = {row['path']: row for row in json.loads(
                (source / 'Meta/engineering-projects.json').read_text())['projects']}
            def expand(patterns, excludes=()):
                include = re.compile('|'.join(selection.compile_glob(p, 'test input').pattern for p in patterns) or '(?!)')
                exclude = re.compile('|'.join(selection.compile_glob(p, 'test exclude').pattern for p in excludes) or '(?!)')
                return {path for path in paths if path and include.fullmatch(path) and not exclude.fullmatch(path)}
            @functools.cache
            def compiled(path):
                row = projects[path]
                return ({path} | expand(row['include'], row['exclude']) | expand(row['build_inputs'])
                    | set().union(*(compiled(ref) for ref in row['references'])))
            project = 'tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj'
            row = projects[project]
            runtime = expand(row['execution_inputs'], row['execution_excludes'])
            compile_inputs = compiled(project)
            # Default Fourier evidence invokes the canonical cache wrapper and native
            # facets. Native preparation consumes all registered source coordinates,
            # not just the two selected modules' direct imports. Reuse the existing
            # report contract here; do not approximate Lean's dependency graph.
            required = set(inputs.producer_paths('lean-report'))
            for group in ('report_modules', 'inspector_sources', 'dependency_sources', 'config_inputs'):
                required.update(inputs.expand(group))
            required.update(compiled('tools/StrataLint.Lean/StrataLint.Lean.csproj'))
            required.update(['tools/scripts/worktree/lean-cache-run.sh',
                'tools/scripts/worktree/lean_cache_release.py', 'tools/scripts/worktree/cache_material.py'])
            assert required <= runtime | compile_inputs, ('untracked native inputs', sorted(required - runtime - compile_inputs))
            for path in ('README.md', 'D5/README.md', 'docs/develop/theory/native-input-control.md',
                    'tools/lean-inspector/tests/test_native.py', 'tools/scripts/workflow/truth_release.py'):
                assert not any(selection.compile_glob(pattern, 'control').fullmatch(path)
                    for pattern in row['execution_inputs']), ('unrelated runtime input', path)
            print(json.dumps({'required_native_inputs': len(required), 'runtime_inputs': len(runtime),
                'compile_inputs': len(compile_inputs), 'native_inputs_outside_compile': len(required - compile_inputs)}, sort_keys=True))
            """);

        Assert.True(result.Exit == 0, result.Text);
        output.WriteLine(result.Text);
    }

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
