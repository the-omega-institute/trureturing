using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanInspectorScriptTests
{
    [Fact]
    public void DeclaredRuntimeMaterialChangesIdentityWithoutDependencyDiscovery()
    {
        using var fixture = new RuntimeFixture();
        var before = fixture.Identity();
        fixture.Write("runtime/lib/lean/Declared.olean", "declared runtime v2");
        Assert.NotEqual(before, fixture.Identity());
        Assert.DoesNotContain("--deps", fixture.Commands, StringComparison.Ordinal);
    }

    [Fact]
    public void UndeclaredLibrariesImportsAndNeighborsDoNotExpandRuntimeAuthority()
    {
        using var fixture = new RuntimeFixture();
        var before = fixture.Identity();
        fixture.Write("runtime/lib/lean/extra.so", "unregistered shared library");
        fixture.Write("runtime/lib/lean/Init.ilean", "{\"directImports\":[\"Undeclared\"]}");
        fixture.Write("runtime/lib/lean/Undeclared.olean", "not registered");
        fixture.Write("runtime/lib/lean/Undeclared.ilean", "{\"directImports\":[]}");
        Assert.Equal(before, fixture.Identity());
    }

    [Theory]
    [InlineData("material", "lib/lean/Declared.olean")]
    [InlineData("glob", "lib/lean/libleanshared.*")]
    [InlineData("declaration", "runtime")]
    [InlineData("duplicate", "bin/lean")]
    [InlineData("overlap", "bin/lean")]
    public void InvalidRuntimeRegistrationFailsAtProducerBoundaryInsteadOfDisablingIncrementality(string defect, string expected)
    {
        using var fixture = new RuntimeFixture();
        if (defect == "material") File.Delete(Path.Combine(fixture.Root, "runtime/lib/lean/Declared.olean"));
        if (defect == "glob") File.Delete(Path.Combine(fixture.Root, "runtime/lib/lean/libleanshared.so"));
        if (defect == "declaration") fixture.Edit(manifest => manifest.AsObject().Remove("runtime"));
        if (defect == "duplicate") fixture.Edit(manifest => manifest["runtime"]!["lean"]!.AsArray().Add("bin/lean"));
        if (defect == "overlap") fixture.Edit(manifest => manifest["runtime"]!["lean"]!.AsArray().Add("bin/*"));
        var identity = fixture.Runtime();
        Assert.Equal(2, identity.ExitCode);
        Assert.Contains(expected, Encoding.UTF8.GetString(identity.StandardError), StringComparison.Ordinal);
        var producer = fixture.Inspect();
        Assert.Equal(2, producer.ExitCode);
        Assert.Contains(expected, Encoding.UTF8.GetString(producer.StandardError), StringComparison.Ordinal);
        Assert.DoesNotContain("--run", fixture.Commands, StringComparison.Ordinal);
    }

    [Fact]
    public void DeclaredRuntimeAndProducerChangesReinspectInsideSamePartitionWhileMetadataReuses()
    {
        using var fixture = new RuntimeFixture();
        fixture.Pair("full-fallback", 2);
        var seed = fixture.SeedIdentity();
        fixture.Pair("reuse", 0);
        fixture.Write("lakefile.toml", "name = \"renamed\"\nkeywords = [\"metadata\"]\n");
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789abcdef0123456789abcdef01234567\",\"inputRev\":\"metadata\"}]}\n");
        fixture.Write("runtime/lib/lean/unregistered.so", "ignored");
        fixture.Pair("reuse", 0);
        Assert.Equal(seed, fixture.SeedIdentity());
        fixture.Write("runtime/lib/lean/Declared.olean", "runtime changed");
        fixture.Pair("delta", 2);
        var changed = fixture.SeedIdentity();
        Assert.Equal(seed.Partition, changed.Partition);
        Assert.NotEqual(seed.Runtime, changed.Runtime);
        fixture.Write("lakefile.toml", "name = \"renamed\"\n[leanOptions]\nmaxRecDepth = 2000\n");
        fixture.Pair("delta", 2);
        fixture.Write("tools/lean-inspector/Inspector.lean", "-- changed producer\n");
        fixture.Pair("delta", 2);
        Assert.Equal(seed.Partition, fixture.SeedIdentity().Partition);
        Assert.Equal(6, fixture.Commands.Split('\n').Count(line => line == "build"));
        Assert.Equal(4, fixture.Commands.Split('\n').Count(line => line.Contains("--run", StringComparison.Ordinal)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AbsentOrCorruptOptionalReportCacheStillExecutesProducer(bool corrupt)
    {
        using var fixture = new RuntimeFixture();
        if (corrupt)
        {
            fixture.Pair("full-fallback", 2);
            foreach (var path in Directory.GetFiles(Path.Combine(fixture.Root, "cache"), "*.materials.zip", SearchOption.AllDirectories))
                File.WriteAllText(path, "corrupt optional cache");
            File.Delete(fixture.Output);
        }
        fixture.Pair("full-fallback", 2);
    }

    private sealed class RuntimeFixture : IDisposable
    {
        private const string Registration = "Meta/ReportProducers/lean-report.json";
        private readonly TemporaryDirectory temporary = new();
        internal string Root { get; }
        private string Lake => Path.Combine(Root, "runtime/bin/lean");
        internal string Output => Path.Combine(Root, "out/report.json");
        internal string Commands => File.Exists(Path.Combine(Root, "lake-runs")) ? File.ReadAllText(Path.Combine(Root, "lake-runs")) : "";
        internal RuntimeFixture()
        {
            Root = CreateRepository(temporary.Path);
            foreach (var path in new[] { "tools/scripts/lean-report-pair.sh", "tools/scripts/report/report-supervisor.sh" })
                File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(Root, path), true);
            Write("runtime/bin/lean", FakeLake);
            if (!OperatingSystem.IsWindows())
                File.SetUnixFileMode(Lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            foreach (var path in new[] { "Init.olean", "Declared.olean", "libleanshared.so" }) Write("runtime/lib/lean/" + path, "runtime-v1");
            Write("runtime/lib/lean/Init.ilean", "{\"directImports\":[]}");
            Edit(manifest => manifest["runtime"] = JsonNode.Parse("""
                {"lean":["bin/lean","lib/lean/Init.olean","lib/lean/Declared.olean","lib/lean/libleanshared.*"],"python":["executable"]}
                """));
            Directory.CreateDirectory(Path.Combine(Root, "cache"));
        }
        internal void Write(string path, string text) => LeanInspectorScriptTests.Write(Root, path, text);
        internal void Edit(Action<JsonNode> change)
        {
            var manifest = JsonNode.Parse(File.ReadAllText(Path.Combine(Root, Registration)))!;
            change(manifest);
            Write(Registration, manifest.ToJsonString());
        }
        internal ProcessOutput Runtime() => Run("python3", [Path.Combine(Root, "tools/lean-inspector/runtime_identity.py"),
            "--repository", Root, "--lake", Lake], Root);
        internal string Identity()
        {
            var result = Runtime();
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
        internal ProcessOutput Inspect() => Run("env", [$"LAKE_BIN={Lake}", Path.Combine(Root, InspectorScript),
            "--repository", Root, "--output", Output], Root);
        internal void Pair(string mode, int recheck)
        {
            var result = Run("env", [$"STRATALINT_SUPERVISOR_ROOT={Path.Combine(temporary.Path, "supervisor")}",
                $"STRATALINT_REPORT_CACHE_ROOT={Path.Combine(Root, "cache")}", Path.Combine(Root, "tools/scripts/lean-report-pair.sh"),
                "--producer", Path.Combine(Root, InspectorScript), "--lake-bin", Lake, "--candidate-root", Root, "--candidate-output", Output], Root);
            var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
            Assert.True(result.ExitCode == 0, output);
            Assert.True(output.Contains($"LEAN_REPORT_DELTA mode={mode} changed=0 added=0 removed=0 recheck={recheck}", StringComparison.Ordinal), output);
        }
        internal (string Partition, string Runtime) SeedIdentity()
        {
            var seed = JsonNode.Parse(File.ReadAllText(Output + ".seed.json"))!;
            return (seed["partition"]!.ToString(), seed["runtime_sha256"]!.ToString());
        }
        public void Dispose() => temporary.Dispose();
        private const string FakeLake = """
            #!/usr/bin/env python3
            import json, pathlib, sys
            args = sys.argv[1:]
            root = pathlib.Path.cwd()
            with (root / "lake-runs").open("a") as log: log.write(" ".join(args) + "\n")
            if args == ["build"]: sys.exit(0)
            if "--print-prefix" in args: print(pathlib.Path(__file__).parent.parent); sys.exit(0)
            if "--deps" in args: print(pathlib.Path(__file__).parent.parent / "lib/lean/Init.olean"); sys.exit(0)
            output = pathlib.Path(args[args.index("--output") + 1])
            values = args[args.index("--utility-input") + 2:]
            modules = [{"module": values[i], "source_path": values[i+1], "source_sha256": values[i+2], "imports": [], "declarations": []}
                       for i in range(0, len(values), 3)]
            output.write_text(json.dumps({"schema":"stratalint-lean-inspector-spool-v1", "modules": sorted(modules, key=lambda row: row["module"])}) + "\n")
            """;
    }
}
