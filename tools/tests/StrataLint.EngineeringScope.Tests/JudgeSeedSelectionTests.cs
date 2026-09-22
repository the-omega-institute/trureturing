using System.Text.Json;
using System.Text.Json.Nodes;
using System.Security.Cryptography;
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

    [Theory]
    [InlineData("unchanged")]
    [InlineData("no-local-material")]
    [InlineData("changed-unselected-source")]
    [InlineData("removed-registration")]
    [InlineData("proof-registration")]
    public void NarrowSnapshotRetainsOnlyDeclaredEligibleDonorProjects(string mode)
    {
        using var fixture = new SeedFixture();
        fixture.Build([SeedFixture.Tests, SeedFixture.Other]);
        Assert.Contains("judge_ready=true", fixture.Snapshot().Text, StringComparison.Ordinal);
        var previous = File.ReadAllBytes(Path.Combine(fixture.Root, "build/lean-cache/judge/data/data", SeedFixture.Other + ".seed"));
        fixture.Build([SeedFixture.Tests]);
        if (mode == "no-local-material")
        {
            fixture.Delete(fixture.Receipt(SeedFixture.Other));
            Directory.Delete(Path.Combine(fixture.Root, "tools/tests/Other.Tests/obj"), recursive: true);
        }
        if (mode == "changed-unselected-source") fixture.Write("tools/tests/Other.Tests/Value.cs", "changed since donor compilation");
        if (mode is "removed-registration" or "proof-registration")
        {
            var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
            var rows = registration["projects"]!.AsArray();
            var other = rows.Single(row => row!["path"]!.GetValue<string>() == SeedFixture.Other)!;
            if (mode == "removed-registration")
            {
                rows.Remove(other);
                SharedBuildContractTests.Git(fixture.Root, "rm", "-rf", "tools/tests/Other.Tests");
            }
            else
            {
                other["role"] = "compile-fail-proof";
                other["ci"] = false;
                foreach (var field in new[] { "test_partition", "execution_inputs", "execution_excludes", "execution_environment", "execution_filemap_paths" }) other[field] = null;
            }
            fixture.Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        }

        var result = fixture.Snapshot();

        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("judge_ready=true", result.Text, StringComparison.Ordinal);
        var material = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/lean-cache/judge/data/material.json")))!;
        var expected = mode is "removed-registration" or "proof-registration"
            ? new[] { SeedFixture.Library, SeedFixture.Tests } : [SeedFixture.Library, SeedFixture.Tests, SeedFixture.Other];
        Assert.Equal(expected.Order(StringComparer.Ordinal), material["projects"]!.AsArray().Select(row => row!.GetValue<string>()));
        if (expected.Contains(SeedFixture.Other))
            Assert.Equal(previous, File.ReadAllBytes(Path.Combine(fixture.Root, "build/lean-cache/judge/data/data", SeedFixture.Other + ".seed")));
        Assert.Equal(new[] { SeedFixture.Tests }, JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/build.json")))!["projects"]!.AsArray().Select(row => row!.GetValue<string>()));
    }

    [Theory]
    [InlineData("partition")]
    [InlineData("key")]
    [InlineData("damaged-object")]
    [InlineData("foreign-root")]
    [InlineData("duplicate-project")]
    [InlineData("invalid-project")]
    [InlineData("unlisted-manifest")]
    [InlineData("unlisted-receipt")]
    [InlineData("unlisted-object")]
    [InlineData("late-undeclared-object")]
    [InlineData("selected-receipt")]
    public void DamagedDonorsFallBackToFreshSelectionWithoutHidingSelectedDefects(string defect)
    {
        using var fixture = new SeedFixture();
        fixture.Build([SeedFixture.Tests, SeedFixture.Other]);
        Assert.Contains("judge_ready=true", fixture.Snapshot().Text, StringComparison.Ordinal);
        fixture.Build(defect == "late-undeclared-object" ? [SeedFixture.Library] : [SeedFixture.Tests]);
        var manifestPath = Path.Combine(fixture.Root, "build/lean-cache/judge/manifest.json");
        var manifest = JsonNode.Parse(File.ReadAllText(manifestPath))!;
        if (defect is "partition" or "key") manifest[defect] = "different";
        if (defect == "damaged-object") fixture.Write("build/lean-cache/judge/data/data/tools/tests/Other.Tests/obj/output.dll", "damaged");
        if (defect == "selected-receipt") fixture.Delete(fixture.Receipt(SeedFixture.Tests));
        if (defect.StartsWith("unlisted-", StringComparison.Ordinal) || defect == "late-undeclared-object")
        {
            var path = defect == "unlisted-manifest" ? "material.json" : defect == "unlisted-receipt"
                ? "data/" + SeedFixture.Other + ".seed" : "data/tools/tests/Other.Tests/obj/output.dll";
            var files = manifest["files"]!.AsArray();
            files.Remove(files.Single(row => row!["path"]!.GetValue<string>() == path));
        }
        if (defect is "foreign-root" or "duplicate-project" or "invalid-project")
        {
            const string relative = "build/lean-cache/judge/data/material.json";
            var material = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, relative)))!;
            if (defect == "foreign-root") material["root"] = fixture.Root + "-foreign";
            else material["projects"]!.AsArray().Add(defect == "duplicate-project" ? SeedFixture.Other : "../outside.csproj");
            fixture.Write(relative, material.ToJsonString());
            manifest["files"]!.AsArray().Single(row => row!["path"]!.GetValue<string>() == "material.json")!["sha256"] =
                Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(Path.Combine(fixture.Root, relative))));
        }
        fixture.Write("build/lean-cache/judge/manifest.json", manifest.ToJsonString());
        var original = File.ReadAllBytes(manifestPath);

        var result = fixture.Snapshot();

        Assert.True(result.Exit == 0, result.Text);
        if (defect == "selected-receipt")
        {
            Assert.Contains("judge_ready=false", result.Text, StringComparison.Ordinal);
            Assert.Equal(original, File.ReadAllBytes(manifestPath));
            return;
        }
        Assert.Contains("judge_ready=true", result.Text, StringComparison.Ordinal);
        var expected = defect == "late-undeclared-object" ? new[] { SeedFixture.Library } : [SeedFixture.Library, SeedFixture.Tests];
        var repairedMaterial = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/lean-cache/judge/data/material.json")))!;
        Assert.Equal(expected.Order(StringComparer.Ordinal), repairedMaterial["projects"]!.AsArray().Select(row => row!.GetValue<string>()));
        var exported = Directory.GetFiles(Path.Combine(fixture.Root, "build/lean-cache/judge/data/data"), "*.csproj.seed", SearchOption.AllDirectories);
        Assert.Equal(expected.Length, exported.Length);
        var restored = fixture.Restore();
        Assert.True(restored.Exit == 0, restored.Text);
        Assert.Contains("\"status\": \"restored\"", restored.Text, StringComparison.Ordinal);
        Assert.Equal(File.ReadAllBytes(Path.Combine(fixture.Root, "build/lean-cache/judge/data/material.json")),
            File.ReadAllBytes(Path.Combine(fixture.Root, ".judge-binaries/material.json")));
    }

    [Fact]
    public void InvalidCandidateRegistrationCannotBecomeAnOptionalDonorMiss()
    {
        using var fixture = new SeedFixture();
        fixture.Build([SeedFixture.Tests]);
        Assert.Contains("judge_ready=true", fixture.Snapshot().Text, StringComparison.Ordinal);
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
        registration["projects"]!.AsArray()[0]!["role"] = "unknown-role";
        fixture.Write(EngineeringRegistrationFixture.Path, registration.ToJsonString());
        fixture.Write("build/lean-cache/judge/manifest.json", "broken donor");

        var result = fixture.Snapshot();

        Assert.NotEqual(0, result.Exit);
        Assert.DoesNotContain("judge_ready=true", result.Text, StringComparison.Ordinal);
        Assert.Equal("broken donor", File.ReadAllText(Path.Combine(fixture.Root, "build/lean-cache/judge/manifest.json")));
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
            Write(".gitignore", "build/\n.judge-binaries/\n**/obj/\n**/bin/\n");
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
        internal (int Exit, string Text) Snapshot(string eventName = "push") => Cache("snapshot", eventName);
        internal (int Exit, string Text) Restore()
        {
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(Root, "build/lean-cache/judge/manifest.json")))!;
            return Cache("restore", "push", "--judge-key", manifest["key"]!.GetValue<string>());
        }
        private (int Exit, string Text) Cache(string command, string eventName, params string[] arguments) => SharedBuildContractTests.Process(Root, "python3",
            ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), command, "--repository", Root, "--layers", "judge", .. arguments],
            new Dictionary<string, string> {
                ["GITHUB_EVENT_NAME"] = eventName, ["GITHUB_REF"] = "refs/heads/integration-ci-fixture-tests",
                ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "1",
                ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_BUILD_SUCCEEDED"] = "true",
                ["STRATALINT_CHECK_SUCCEEDED"] = "false", ["GITHUB_OUTPUT"] = "",
            });
        public void Dispose() => TemporaryFileSystem.Directory.Delete(Root, recursive: true);
    }
}
