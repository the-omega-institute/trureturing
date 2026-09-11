using System.Runtime.Versioning;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Xunit.Abstractions;

namespace StrataLint.Tests;

[UnsupportedOSPlatform("windows")]
public sealed class LeanDependencyCacheScriptTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData(0)]
    [InlineData(9)]
    public void DeclaredDependencySeedIgnoresUnlistedNeighborAndRunsProduction(int producerExit)
    {
        using var fixture = new DependencyFixture(output);
        fixture.Snapshot();
        fixture.ChangeCurrentMaterial();
        fixture.AssertMaterial(fixture.Cached, fixture.Material);
        File.WriteAllBytes(Path.Combine(fixture.Cached, "batteries/extra"), "unlisted"u8.ToArray());

        var result = fixture.Produce(producerExit);

        fixture.AssertProduction(result, producerExit);
        var receipt = fixture.DependencyReceipt(result);
        Assert.Equal("restored", receipt.GetProperty("status").GetString());
        Assert.False(receipt.TryGetProperty("reason", out _));
        Assert.False(File.Exists(Path.Combine(fixture.Source, "batteries/extra")));
        fixture.AssertMaterial(fixture.Source, fixture.Material);
        fixture.AssertPrivateCopies();
    }

    [Theory]
    [InlineData("bytes", 0)]
    [InlineData("bytes", 9)]
    [InlineData("mode", 0)]
    [InlineData("mode", 9)]
    [InlineData("link", 0)]
    [InlineData("link", 9)]
    [InlineData("missing", 0)]
    [InlineData("missing", 9)]
    public void CorruptListedDependencySeedPreservesCurrentMaterialAndRunsProduction(string corruption, int producerExit)
    {
        using var fixture = new DependencyFixture(output);
        fixture.Snapshot();
        var current = fixture.ChangeCurrentMaterial();
        var saved = Path.Combine(fixture.Cached, "batteries/README.md");
        switch (corruption)
        {
            case "bytes": File.WriteAllBytes(saved, "corrupted bytes"u8.ToArray()); break;
            case "mode": File.SetUnixFileMode(saved, DependencyFixture.ExecutableMode); break;
            case "link":
                File.Delete(saved);
                File.CreateSymbolicLink(saved, "README.copy");
                break;
            case "missing": File.Delete(saved); break;
            default: throw new ArgumentOutOfRangeException(nameof(corruption));
        }

        var result = fixture.Produce(producerExit);

        fixture.AssertProduction(result, producerExit);
        var receipt = fixture.DependencyReceipt(result);
        Assert.Equal("miss", receipt.GetProperty("status").GetString());
        Assert.Contains("batteries/README.md", receipt.GetProperty("reason").GetString(), StringComparison.Ordinal);
        fixture.AssertMaterial(fixture.Source, current);
    }

    private sealed class DependencyFixture : IDisposable
    {
        internal const UnixFileMode ExecutableMode = UnixFileMode.UserRead | UnixFileMode.UserWrite |
            UnixFileMode.UserExecute | UnixFileMode.GroupRead | UnixFileMode.GroupExecute |
            UnixFileMode.OtherRead | UnixFileMode.OtherExecute;
        private const UnixFileMode PrivateMode = UnixFileMode.UserRead | UnixFileMode.UserWrite;
        private readonly TemporaryDirectory temporary = new();
        private readonly ITestOutputHelper output;
        private readonly string owner = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py");
        private string key = "";
        internal string Source => Path.Combine(temporary.Path, ".lake/packages");
        internal string Cached => Path.Combine(temporary.Path, "build/lean-cache/dependency/data");
        internal MaterialRow[] Material { get; } =
        [
            new("mathlib/scripts/bench/size/run", "#!/bin/sh\nprintf 'size\\n'\n"u8.ToArray(), ExecutableMode),
            new("mathlib/scripts/bench/build/fake-root/bin/lean", "#!/bin/sh\nexit 0\n"u8.ToArray(), ExecutableMode),
            new("batteries/README.md", [.."# Batteries\n\0private bytes"u8, 0xff, 0x0a], PrivateMode | UnixFileMode.GroupRead),
            new("batteries/README.copy", [.."# Batteries\n\0private bytes"u8, 0xff, 0x0a], PrivateMode | UnixFileMode.GroupRead),
            new("batteries/private", "private regular file"u8.ToArray(), PrivateMode),
        ];

        internal DependencyFixture(ITestOutputHelper output)
        {
            this.output = output;
            ScriptHarnessScratch.WriteScratchText(Path.Combine(temporary.Path, "lake-manifest.json"),
                JsonSerializer.Serialize(new { packages = new[] { new { name = "mathlib", rev = new string('a', 40) } } }));
            ScriptHarnessScratch.WriteScratchText(Path.Combine(temporary.Path, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
            ScriptHarnessScratch.WriteScratchText(Path.Combine(temporary.Path, "Makefile"),
                "current:\n\t@printf 'producer:%s\\n' \"$$PRODUCER_EXIT\" >> calls\n\t@exit \"$$PRODUCER_EXIT\"\n");
            foreach (var row in Material) WriteMaterial(Source, row);
        }

        internal void Snapshot()
        {
            var result = Run(["python3", owner, "snapshot", "--repository", temporary.Path, "--layers", "dependency"]);
            Assert.True(result.ExitCode == 0, result.Text);
            Assert.Equal("dependency_ready=true\n", File.ReadAllText(Path.Combine(temporary.Path, "outputs")));
            Assert.Equal("snapshot", DependencyReceipt(result).GetProperty("status").GetString());
            using var manifest = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(Cached, "../manifest.json")));
            Assert.Equal("lean-actions-seed-v1", manifest.RootElement.GetProperty("schema").GetString());
            key = manifest.RootElement.GetProperty("key").GetString()!;
            var rows = manifest.RootElement.GetProperty("files").EnumerateArray().ToArray();
            Assert.Equal(Material.OrderBy(row => row.Path, StringComparer.Ordinal).Select(row => row.Path),
                rows.Select(row => row.GetProperty("path").GetString()));
            foreach (var expected in Material)
            {
                var row = Assert.Single(rows, row => row.GetProperty("path").GetString() == expected.Path);
                Assert.Equal(Convert.ToHexStringLower(SHA256.HashData(expected.Bytes)), row.GetProperty("sha256").GetString());
                Assert.Equal((int)expected.Mode, row.GetProperty("mode").GetInt32());
            }
            AssertMaterial(Cached, Material);
        }

        internal MaterialRow[] ChangeCurrentMaterial()
        {
            var current = Material.Select(row => row.Path == "batteries/README.md"
                ? row with { Bytes = "current material"u8.ToArray(), Mode = PrivateMode } : row).ToArray();
            foreach (var row in current) WriteMaterial(Source, row);
            return current;
        }

        internal Attempt Produce(int producerExit) => Run(
            ["bash", "-euc", "\"$PYTHON\" \"$CACHE\" restore --repository \"$ROOT\" --dependency-key \"$KEY\"; make -C \"$ROOT\" current"],
            producerExit);

        internal void AssertProduction(Attempt result, int producerExit)
        {
            // make preserves failure as exit 2; its recipe's actual exit is also reported.
            Assert.Equal(producerExit == 0 ? 0 : 2, result.ExitCode);
            if (producerExit != 0) Assert.Contains($"Error {producerExit}", result.Text, StringComparison.Ordinal);
            Assert.Equal($"producer:{producerExit}\n", File.ReadAllText(Path.Combine(temporary.Path, "calls")));
            Assert.Equal("STRATALINT_ACTIONS_CACHE_SEEDED=0\n", File.ReadAllText(Path.Combine(temporary.Path, "environment")));
            output.WriteLine($"producer_exit={producerExit} command_exit={result.ExitCode} normalized_exit={(result.ExitCode == 0 ? 0 : 1)} calls=1");
        }

        internal JsonElement DependencyReceipt(Attempt result)
        {
            var line = Assert.Single(result.Text.Split('\n').Where(line => line.StartsWith("LEAN_ACTIONS_CACHE ", StringComparison.Ordinal))
                .Select(line => JsonSerializer.Deserialize<JsonElement>(line["LEAN_ACTIONS_CACHE ".Length..])),
                row => row.GetProperty("layer").GetString() == "dependency");
            return line;
        }

        internal void AssertMaterial(string directory, MaterialRow[] expected)
        {
            Assert.Equal(expected.Select(row => row.Path).Order(StringComparer.Ordinal),
                Directory.GetFiles(directory, "*", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(directory, path)).Order(StringComparer.Ordinal));
            foreach (var row in expected)
            {
                var path = Path.Combine(directory, row.Path);
                Assert.Null(new FileInfo(path).LinkTarget);
                Assert.Equal(row.Bytes, File.ReadAllBytes(path));
                Assert.Equal(row.Mode, File.GetUnixFileMode(path));
            }
        }

        internal void AssertPrivateCopies()
        {
            foreach (var row in Material)
            {
                var source = Path.Combine(Source, row.Path);
                var cached = Path.Combine(Cached, row.Path);
                var changed = row with { Bytes = "changed consumer bytes"u8.ToArray(), Mode = PrivateMode | UnixFileMode.OtherRead };
                WriteMaterial(Source, changed);
                Assert.Equal(row.Bytes, File.ReadAllBytes(cached));
                Assert.Equal(row.Mode, File.GetUnixFileMode(cached));
                WriteMaterial(Source, row);
                WriteMaterial(Cached, changed with { Bytes = "changed cache bytes"u8.ToArray() });
                Assert.Equal(row.Bytes, File.ReadAllBytes(source));
                Assert.Equal(row.Mode, File.GetUnixFileMode(source));
            }
        }

        private static void WriteMaterial(string directory, MaterialRow row)
        {
            var path = Path.Combine(directory, row.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, row.Bytes);
            File.SetUnixFileMode(path, row.Mode);
        }

        private Attempt Run(string[] command, int producerExit = 0)
        {
            var result = TestProcessRunner.Run("/usr/bin/env",
                ["GITHUB_RUN_ID=17", "GITHUB_RUN_ATTEMPT=2", "GITHUB_EVENT_NAME=push", "GITHUB_REF=refs/heads/dev",
                    "STRATALINT_CHECK_SUCCEEDED=true", "STRATALINT_CACHE_WRITES=true", "MAKEFLAGS=", "MAKELEVEL=0",
                    $"GITHUB_OUTPUT={Path.Combine(temporary.Path, "outputs")}", $"GITHUB_ENV={Path.Combine(temporary.Path, "environment")}",
                    "PYTHON=python3", $"CACHE={owner}", $"ROOT={temporary.Path}", $"KEY={key}", $"PRODUCER_EXIT={producerExit}", ..command],
                temporary.Path, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
            var attempt = new Attempt(result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
            output.WriteLine(attempt.Text);
            return attempt;
        }

        public void Dispose() => temporary.Dispose();
        internal sealed record MaterialRow(string Path, byte[] Bytes, UnixFileMode Mode);
        internal sealed record Attempt(int ExitCode, string Text);
    }
}
