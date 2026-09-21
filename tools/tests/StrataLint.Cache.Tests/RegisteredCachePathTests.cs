using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.Cache.Tests;

public sealed class RegisteredCachePathTests
{
    [Fact]
    public void NativeArchivePathsComeOnlyFromTheRegisteredLayer()
    {
        using var fixture = new Fixture();
        string[] paths = [".lake/build/lib", ".lake/build/ir/**/*.c", ".lake/build/ir/**/*.c.hash"];
        fixture.Manifest(paths);
        Directory.CreateDirectory(Path.Combine(fixture.Root, ".lake/build/unregistered"));
        File.WriteAllText(Path.Combine(fixture.Root, ".lake/build/unregistered/large.setup.json"), "unselected");
        var result = fixture.Keys("project");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(string.Join('\n', paths.Order(StringComparer.Ordinal)), ReadOutput(result.Output, "project_archive_path"));
        Assert.Equal(".lake/build", ReadOutput(result.Output, "project_path"));
        Assert.DoesNotContain("dependency_archive_path", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing-file")]
    [InlineData("unregistered-file")]
    [InlineData("missing-layer")]
    [InlineData("duplicate-layer")]
    [InlineData("unknown-layer")]
    [InlineData("unsupported-schema")]
    [InlineData("empty-paths")]
    [InlineData("duplicate-paths")]
    [InlineData("wrong-root")]
    [InlineData("parent-path")]
    [InlineData("absolute-path")]
    [InlineData("newline")]
    public void InvalidRegistrationCannotBecomeAnOptionalCacheMiss(string defect)
    {
        using var fixture = new Fixture();
        fixture.Manifest([".lake/build/lib"]);
        switch (defect)
        {
            case "missing-file": File.Delete(fixture.ManifestPath); break;
            case "unregistered-file": File.WriteAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"), "files = []\n"); break;
            case "missing-layer": fixture.Raw("{\"schema_version\":1,\"layers\":{\"dependency\":[\".lake/packages\"]}}"); break;
            case "duplicate-layer": fixture.Raw("{\"schema_version\":1,\"layers\":{\"project\":[\".lake/build/lib\"],\"project\":[\".lake/build/ir\"]}}"); break;
            case "unknown-layer": fixture.Raw("{\"schema_version\":1,\"layers\":{\"guess\":[\".lake/build/lib\"]}}"); break;
            case "unsupported-schema": fixture.Raw("{\"schema_version\":2,\"layers\":{\"project\":[\".lake/build/lib\"]}}"); break;
            case "empty-paths": fixture.Manifest([]); break;
            case "duplicate-paths": fixture.Manifest([".lake/build/lib", ".lake/build/lib"]); break;
            case "wrong-root": fixture.Manifest([".lake/packages"]); break;
            case "parent-path": fixture.Manifest([".lake/build/../outside"]); break;
            case "absolute-path": fixture.Manifest(["/tmp/material"]); break;
            case "newline": fixture.Manifest([".lake/build/lib\nother=value"]); break;
        }
        var result = fixture.Keys("project");
        Assert.True(result.Exit == 2, result.Text);
        Assert.Contains("cache path registration", result.Text, StringComparison.Ordinal);
        Assert.Empty(result.Output);
    }

    [Fact]
    public void ArchiveLayoutChangesDoNotCreateAnotherMathlibPartition()
    {
        using var fixture = new Fixture();
        fixture.Manifest([".lake/build/lib"]);
        var before = fixture.Keys("project");
        fixture.Manifest([".lake/build/lib", ".lake/build/lean-inspector"]);
        var after = fixture.Keys("project");
        Assert.True(before.Exit == 0 && after.Exit == 0, before.Text + after.Text);
        foreach (var key in new[] { "mathlib_revision", "partition", "project_key", "project_restore_prefix" })
            Assert.Equal(ReadOutput(before.Output, key), ReadOutput(after.Output, key));
        Assert.NotEqual(ReadOutput(before.Output, "project_archive_path"), ReadOutput(after.Output, "project_archive_path"));
        fixture.Manifest([".lake/build/lean-inspector", ".lake/build/lib"]);
        var reordered = fixture.Keys("project");
        Assert.True(reordered.Exit == 0, reordered.Text);
        Assert.Equal(ReadOutput(after.Output, "project_archive_path"), ReadOutput(reordered.Output, "project_archive_path"));
    }

    [Fact]
    public void NonNativeLayerDoesNotRequireUnselectedNativeRegistration()
    {
        using var fixture = new Fixture();
        var result = fixture.Keys("judge");
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal("build/lean-cache/judge", ReadOutput(result.Output, "judge_path"));
        Assert.DoesNotContain("project_archive_path", result.Output, StringComparison.Ordinal);
    }

    private static string ReadOutput(string commands, string key)
    {
        var lines = commands.Split('\n');
        for (var index = 0; index < lines.Length; index++)
        {
            if (lines[index].StartsWith(key + "=", StringComparison.Ordinal)) return lines[index][(key.Length + 1)..];
            if (!lines[index].StartsWith(key + "<<", StringComparison.Ordinal)) continue;
            var delimiter = lines[index][(key.Length + 2)..];
            return string.Join('\n', lines.Skip(index + 1).TakeWhile(line => line != delimiter));
        }
        Assert.Fail("Missing output: " + key);
        return "";
    }

    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        internal string Root => temporary.Path;
        internal string ManifestPath => Path.Combine(Root, "Meta/ci-cache-paths.json");
        internal Fixture()
        {
            Directory.CreateDirectory(Path.Combine(Root, "Meta"));
            File.WriteAllText(Path.Combine(Root, "lake-manifest.json"), "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"" + new string('a', 40) + "\"}]}");
            File.WriteAllText(Path.Combine(Root, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
            File.WriteAllText(Path.Combine(Root, "Meta/FILEMAP.toml"), "files = [{pattern = \"Meta/ci-cache-paths.json\", consumed_by = [\"automation\"]}]\n");
        }
        internal void Manifest(string[] paths) => Raw(JsonSerializer.Serialize(new
        {
            schema_version = 1, layers = new { dependency = new[] { ".lake/packages" }, project = paths }
        }));
        internal void Raw(string value) => File.WriteAllText(ManifestPath, value);
        internal (int Exit, string Text, string Output) Keys(string layer)
        {
            var output = Path.Combine(Root, "outputs");
            File.Delete(output);
            var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py");
            var result = TestProcessRunner.Run("env", ["GITHUB_RUN_ID=17", "GITHUB_RUN_ATTEMPT=1", "GITHUB_OUTPUT=" + output,
                "python3", "-B", script, "keys", "--repository", Root, "--layers", layer], Root,
                TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
            return (result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError),
                File.Exists(output) ? File.ReadAllText(output) : "");
        }
        public void Dispose() => temporary.Dispose();
    }
}
