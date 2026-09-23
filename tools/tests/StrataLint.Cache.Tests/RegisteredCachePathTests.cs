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
        fixture.Manifest([".lake/build/lib", ".lake/build/lean-inspector", ".lake/build/reg"]);
        var after = fixture.Keys("project");
        Assert.True(before.Exit == 0 && after.Exit == 0, before.Text + after.Text);
        foreach (var key in new[] { "mathlib_revision", "partition", "project_key", "project_restore_prefix" })
            Assert.Equal(ReadOutput(before.Output, key), ReadOutput(after.Output, key));
        Assert.NotEqual(ReadOutput(before.Output, "project_archive_path"), ReadOutput(after.Output, "project_archive_path"));
        fixture.Manifest([".lake/build/reg", ".lake/build/lean-inspector", ".lake/build/lib"]);
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

    [Theory]
    [InlineData("available")]
    [InlineData("missing")]
    [InlineData("symlink")]
    [InlineData("partition")]
    [InlineData("occupied")]
    [InlineData("archive-failure")]
    [InlineData("extract-failure")]
    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    public void DependencyStageUsesRegisteredMaterialAndKeepsProjectCold(string state)
    {
        using var fixture = new Fixture();
        fixture.Manifest([".lake/build/lib"]);
        using var target = new TemporaryDirectory();
        foreach (var path in new[] { "lake-manifest.json", "lean-toolchain" })
            File.Copy(Path.Combine(fixture.Root, path), Path.Combine(target.Path, path));
        var packages = Path.Combine(fixture.Root, ".lake/packages");
        Directory.CreateDirectory(packages);
        var upstream = Path.Combine(packages, "upstream.olean");
        File.WriteAllText(upstream, "transport contract fixture bytes");
        // Selection follows Lake ownership, never filename extensions. Keep
        // checkout identity and source; canonical cache-get owns regeneration
        // of the omitted package work directory, including its non-olean files.
        Directory.CreateDirectory(Path.Combine(packages, "upstream/.git"));
        File.WriteAllText(Path.Combine(packages, "upstream/.git/HEAD"), "pinned checkout identity");
        File.WriteAllText(Path.Combine(packages, "upstream/Source.lean"), "upstream source");
        Directory.CreateDirectory(Path.Combine(packages, "upstream/.lake/build/lib/lean"));
        File.WriteAllText(Path.Combine(packages, "upstream/.lake/build/lib/lean/Source.olean"), "regenerated by cache-get");
        File.WriteAllText(Path.Combine(packages, "upstream/.lake/build/generated.c"), "also regenerated");
        Directory.CreateDirectory(Path.Combine(fixture.Root, ".lake/build/lib"));
        File.WriteAllText(Path.Combine(fixture.Root, ".lake/build/lib/project.olean"), "must stay cold");
        File.WriteAllText(Path.Combine(fixture.Root, ".lake/.stratalint-lean-cache-stamp.json"), "must not mint identity");
        if (state == "missing") Directory.Delete(packages, recursive: true);
        if (state == "symlink") File.CreateSymbolicLink(Path.Combine(packages, "link"), "upstream.olean");
        if (state == "partition") File.WriteAllText(Path.Combine(target.Path, "lake-manifest.json"),
            File.ReadAllText(Path.Combine(target.Path, "lake-manifest.json")).Replace(new string('a', 40), new string('b', 40)));
        if (state == "occupied") Directory.CreateDirectory(Path.Combine(target.Path, ".lake"));
        var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py");
        var environment = new List<string>();
        if (state is "archive-failure" or "extract-failure")
        {
            var bin = Path.Combine(fixture.Root, "bin");
            Directory.CreateDirectory(bin);
            // Complete the real transfer, then report failure. Neither end of
            // the stream may publish even when all expected bytes arrived.
            var stub = Path.Combine(bin, "tar");
            File.WriteAllText(stub,
                "#!/bin/sh\n/usr/bin/tar \"$@\" || exit $?\n"
                + "for arg in \"$@\"; do\n"
                + "  if [ \"$arg\" = \"" + (state == "archive-failure" ? "-cf" : "-xf") + "\" ]; then exit 41; fi\n"
                + "done");
            File.SetUnixFileMode(stub, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            environment.Add("PATH=" + bin + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"));
        }
        var result = TestProcessRunner.Run("env", [.. environment, "python3", "-B", script, "stage-dependency", "--repository", fixture.Root,
            "--destination", target.Path], fixture.Root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.True((result.ExitCode == 0) == (state is "available" or "symlink"), text);
        Assert.False(Directory.Exists(Path.Combine(target.Path, ".lake/build")));
        Assert.False(File.Exists(Path.Combine(target.Path, ".lake/.stratalint-lean-cache-stamp.json")));
        if (state is "available" or "symlink")
        {
            Assert.Equal("pinned checkout identity", File.ReadAllText(Path.Combine(target.Path, ".lake/packages/upstream/.git/HEAD")));
            Assert.Equal("upstream source", File.ReadAllText(Path.Combine(target.Path, ".lake/packages/upstream/Source.lean")));
            Assert.False(Directory.Exists(Path.Combine(target.Path, ".lake/packages/upstream/.lake")));
            if (state == "symlink") Assert.Equal("upstream.olean",
                new FileInfo(Path.Combine(target.Path, ".lake/packages/link")).LinkTarget);
            var copied = Path.Combine(target.Path, ".lake/packages/upstream.olean");
            Assert.Equal(File.ReadAllText(upstream), File.ReadAllText(copied));
            File.WriteAllText(copied, "private edit");
            Assert.Equal("transport contract fixture bytes", File.ReadAllText(upstream));
            File.WriteAllText(upstream, "provider edit");
            Assert.Equal("private edit", File.ReadAllText(copied));
        }
        else
        {
            Assert.False(Directory.Exists(Path.Combine(target.Path, ".lake/packages")));
            Assert.Empty(Directory.GetDirectories(target.Path, ".dependency-*"));
        }
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
