using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class JudgeSeedSelectionTests
{
    [Theory]
    [InlineData("ci-default")]
    [InlineData("partial")]
    [InlineData("explicit-excluded")]
    [InlineData("unselected-corrupt")]
    public void ActionsSnapshotUsesOnlySealedRootsAndRegisteredReferences(string mode)
    {
        using var fixture = new SeedFixture();
        var roots = mode == "ci-default" ? new[] { SeedFixture.Tests, SeedFixture.Other }
            : mode == "explicit-excluded" ? [SeedFixture.ScriptTests] : new[] { SeedFixture.Tests };
        var expected = mode == "ci-default" ? new[] { SeedFixture.Library, SeedFixture.Other, SeedFixture.Tests }
            : mode == "explicit-excluded" ? [SeedFixture.ScriptTests] : new[] { SeedFixture.Library, SeedFixture.Tests };
        fixture.Build(roots);
        foreach (var project in SeedFixture.Projects.Except(expected))
            if (mode == "unselected-corrupt") fixture.Write(fixture.Receipt(project), "broken receipt");
            else fixture.Delete(fixture.Receipt(project));

        var result = fixture.Snapshot();

        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("judge_ready=true", result.Text, StringComparison.Ordinal);
        var material = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/lean-cache/judge/data/material.json")))!;
        Assert.NotNull(material["projects"]);
        Assert.Equal(expected.Order(StringComparer.Ordinal), material["projects"]!.AsArray().Select(item => item!.GetValue<string>()));
        var exported = Directory.GetFiles(Path.Combine(fixture.Root, "build/lean-cache/judge/data/data"), "*.csproj.seed", SearchOption.AllDirectories);
        Assert.Equal(expected.Length, exported.Length);
        Assert.All(expected, project => Assert.True(File.Exists(Path.Combine(fixture.Root, "build/lean-cache/judge/data/data", project + ".seed"))));
    }

    [Theory]
    [InlineData("missing-root", "no successful compiled seed receipt")]
    [InlineData("missing-dependency", "no successful compiled seed receipt")]
    [InlineData("malformed-receipt", "compiled seed receipt")]
    [InlineData("missing-material", "compiled seed receipt")]
    [InlineData("damaged-object", "integrity mismatch")]
    [InlineData("empty-roots", "build project selection")]
    [InlineData("duplicate-roots", "build project selection")]
    [InlineData("unknown-root", "unregistered selected project")]
    [InlineData("missing-build", "build.json")]
    public void SelectedSeedDefectsCannotPublishAnIncompleteSnapshot(string defect, string diagnostic)
    {
        using var fixture = new SeedFixture();
        fixture.Build([SeedFixture.Tests]);
        switch (defect)
        {
            case "missing-root": fixture.Delete(fixture.Receipt(SeedFixture.Tests)); break;
            case "missing-dependency": fixture.Delete(fixture.Receipt(SeedFixture.Library)); break;
            case "malformed-receipt": fixture.Write(fixture.Receipt(SeedFixture.Tests), "broken receipt"); break;
            case "missing-material":
                var receipt = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, fixture.Receipt(SeedFixture.Tests))))!;
                receipt.AsObject().Remove("material");
                fixture.Write(fixture.Receipt(SeedFixture.Tests), receipt.ToJsonString());
                break;
            case "damaged-object": fixture.Write("tools/FixtureLibrary/obj/output.dll", "changed object"); break;
            case "empty-roots": fixture.Build([]); break;
            case "duplicate-roots": fixture.Build([SeedFixture.Tests, SeedFixture.Tests]); break;
            case "unknown-root": fixture.Build(["tools/Absent/Absent.csproj"]); break;
            case "missing-build": fixture.Delete("build/ci/build.json"); break;
        }

        var result = fixture.Snapshot();

        Assert.True(result.Exit == 0, result.Text); // An optional save failure is reported, never a build verdict.
        Assert.Contains("judge_ready=false", result.Text, StringComparison.Ordinal);
        Assert.Contains(diagnostic, result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/lean-cache/judge/manifest.json")));
    }

    [Fact]
    public void PullRequestCannotWriteACompilationSnapshot()
    {
        using var fixture = new SeedFixture();
        fixture.Build([SeedFixture.Tests]);
        var result = fixture.Snapshot("pull_request_target");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("save-disabled", result.Text, StringComparison.Ordinal);
        Assert.Contains("judge_ready=false", result.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache/judge")));
    }

    private sealed class SeedFixture : IDisposable
    {
        internal const string Library = "tools/FixtureLibrary/FixtureLibrary.csproj";
        internal const string Tests = "tools/tests/Fixture.Tests/Fixture.Tests.csproj";
        internal const string Other = "tools/tests/Other.Tests/Other.Tests.csproj";
        internal const string ScriptTests = "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";
        internal static readonly string[] Projects = [Library, Tests, Other, ScriptTests];
        internal string Root { get; } = TemporaryFileSystem.Directory.CreateTempSubdirectory("judge-seed-selection-").FullName;

        internal SeedFixture()
        {
            Write(".gitignore", "build/\n**/obj/\n**/bin/\n");
            Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"}]}\n");
            foreach (var project in Projects)
            {
                Write(project, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
                Write(Path.GetDirectoryName(project) + "/Value.cs", "namespace Fixture; public class Value {}\n");
            }
            Write(EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest(
                new(Library, "FixtureLibrary", "production", false, ["tools/FixtureLibrary/*.cs"], OwnedTestAssembly: "Fixture.Tests"),
                new(Tests, "Fixture.Tests", "cross-cutting-test", true, ["tools/tests/Fixture.Tests/*.cs"], References: [Library]),
                new(Other, "Other.Tests", "cross-cutting-test", true, ["tools/tests/Other.Tests/*.cs"]),
                new(ScriptTests, "StrataLint.ScriptTests", "cross-cutting-test", false, ["tools/tests/StrataLint.ScriptTests/*.cs"])));
            // Real seal() produces receipts for synthetic compiler output. The existing
            // SharedBuildRuntimeTests separately proves cold/warm behavior with Csc.
            var prepared = SharedBuildContractTests.Process(Root, "python3", ["-B", "-c", """
                import pathlib, subprocess, sys, xml.etree.ElementTree as ET, json
                root, source = map(pathlib.Path, sys.argv[1:3])
                sys.path.insert(0, str(source / 'tools/scripts/report'))
                import dotnet_producer
                subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
                subprocess.run(['git', 'add', '.'], cwd=root, check=True)
                for relative in json.loads(sys.argv[3]):
                    project = root / relative
                    obj = project.parent / 'obj'
                    obj.mkdir()
                    output = obj / 'output.dll'
                    output.write_bytes(b'synthetic compiled material')
                    context = ET.Element('compile', root=str(root.resolve()), project=str(project.resolve()), obj=str(obj.resolve()))
                    for field in ('arguments', 'environment', 'runtime', 'configuration'):
                        ET.SubElement(context, field).text = 'fixture'
                    ET.SubElement(ET.SubElement(context, 'inputs'), 'file').text = str((project.parent / 'Value.cs').resolve())
                    ET.SubElement(ET.SubElement(context, 'outputs'), 'file').text = str(output.resolve())
                    capture = root / 'build/capture.xml'
                    capture.parent.mkdir(exist_ok=True)
                    ET.ElementTree(context).write(capture)
                    dotnet_producer.seal(capture)
                task = root / 'build/judge-seed/task'
                task.mkdir(parents=True)
                (task / 'task.dll').write_bytes(b'synthetic task material')
                """, Root, TestRepositoryLayout.FindRoot(), JsonSerializer.Serialize(Projects)]);
            Assert.True(prepared.Exit == 0, prepared.Text);
        }

        internal void Build(string[] projects) => Write("build/ci/build.json", JsonSerializer.Serialize(new
        {
            version = 2, candidate = new string('a', 64), round = "fixture", projects,
            steps = projects.SelectMany(_ => new[] { "restore-StrataLint", "build" }).Select(name => new { name, raw_exit = 0, exit = 0, status = "executed", log = "build/ci/build.log" }),
            materials = Array.Empty<object>(), selection = (object?)null,
        }));

        internal string Receipt(string project) => "build/judge-seed/receipts/" + project + ".seed.json";
        internal void Write(string path, string contents)
        {
            var target = Path.Combine(Root, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            TemporaryFileSystem.File.WriteAllText(target, contents);
        }
        internal void Delete(string path) => TemporaryFileSystem.File.Delete(Path.Combine(Root, path));
        internal (int Exit, string Text) Snapshot(string eventName = "push") => SharedBuildContractTests.Process(Root, "python3",
            ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "snapshot", "--repository", Root, "--layers", "judge"],
            new Dictionary<string, string> {
                ["GITHUB_EVENT_NAME"] = eventName, ["GITHUB_REF"] = "refs/heads/integration-ci-fixture-tests",
                ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "1",
                ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_BUILD_SUCCEEDED"] = "true",
                ["STRATALINT_CHECK_SUCCEEDED"] = "false", ["GITHUB_OUTPUT"] = "",
            });
        public void Dispose() => TemporaryFileSystem.Directory.Delete(Root, recursive: true);
    }
}
