using StrataLint.Runtime;
using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed class LeanCacheDedupeScriptTests
{
    // A main checkout (donor) and one linked worktree; each .lake/build/lib holds an artifact
    // byte-identical to the donor (independent copy with an old mtime), one that differs,
    // and one below the size floor.
    private const string Fixture = """
        set -euo pipefail
        cd "$FIXTURE"
        fill() { python3 -I -c 'import sys; sys.stdout.write((sys.argv[1] * 262144)[:262144])' "$1"; }
        git init -q main
        git -C main -c user.name=t -c user.email=t@t commit -q --allow-empty -m init
        git -C main worktree add -q ../wt
        mkdir -p main/.lake/build/lib wt/.lake/build/lib home
        fill donor > main/.lake/build/lib/Same.olean
        cp main/.lake/build/lib/Same.olean wt/.lake/build/lib/Same.olean
        touch -t 202001020304 wt/.lake/build/lib/Same.olean
        fill other > main/.lake/build/lib/Diff.olean
        fill local > wt/.lake/build/lib/Diff.olean
        printf small > main/.lake/build/lib/Small.ilean
        printf small > wt/.lake/build/lib/Small.ilean
        """;

    private const string Facts = """
        lib="$FIXTURE/wt/.lake/build/lib"
        printf 'same_bytes=%s\n' "$(cmp -s "$lib/Same.olean" "$FIXTURE/main/.lake/build/lib/Same.olean" && echo 1 || echo 0)"
        printf 'diff_bytes=%s\n' "$(fill local | cmp -s - "$lib/Diff.olean" && echo 1 || echo 0)"
        printf 'same_mtime=%s\n' "$(stat -f %Sm -t %Y%m%d%H%M "$lib/Same.olean")"
        printf 'staging=%s\n' "$(find "$lib" -name '.lean-cache-dedupe-*' | wc -l | tr -d ' ')"
        """;

    [Fact]
    public void IdenticalArtifactIsResharedAndDifferingArtifactIsKept()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();

        var output = Run(fixture, Fixture + "\n" + Dedupe("--root wt") + "\n" + Dedupe("--root wt") + "\n" + Facts);

        var receipts = Receipts(output);
        Assert.Equal(2, receipts.Length);
        Assert.Equal("completed", receipts[0].GetProperty("status").GetString());
        Assert.Equal(1, receipts[0].GetProperty("files_relinked").GetInt32());
        Assert.Equal(262144, receipts[0].GetProperty("bytes_relinked").GetInt64());
        Assert.Equal(1, receipts[0].GetProperty("files_differ").GetInt32());
        Assert.Equal(0, receipts[0].GetProperty("files_already_shared").GetInt32());
        Assert.Equal(0, receipts[1].GetProperty("files_relinked").GetInt32());
        Assert.Equal(1, receipts[1].GetProperty("files_already_shared").GetInt32());
        Assert.Contains("same_bytes=1", output, StringComparison.Ordinal);
        Assert.Contains("diff_bytes=1", output, StringComparison.Ordinal);
        Assert.Contains("same_mtime=202001020304", output, StringComparison.Ordinal);
        Assert.Contains("staging=0", output, StringComparison.Ordinal);
    }

    [Fact]
    public void BusyTargetWriterGuardSkipsTheTree()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();
        // Holds the canonical writer guard of the worktree .lake for the whole dedupe run.
        const string holdGuard = """
            lake="$(cd "$FIXTURE/wt/.lake" && pwd -P)"
            guard="$HOME/.cache/stratalint-lean-cache-guards/$(printf %s "$lake" | shasum -a 256 | cut -d' ' -f1).lock"
            mkdir -p "$(dirname "$guard")"
            python3 -I -c 'import fcntl, os, subprocess, sys
            fd = os.open(sys.argv[1], os.O_RDWR | os.O_CREAT)
            fcntl.flock(fd, fcntl.LOCK_EX)
            sys.exit(subprocess.call(sys.argv[2:]))' "$guard" python3 -B "$SCRIPT" --root "$FIXTURE/wt"
            """;

        var output = Run(fixture, Fixture + "\n" + holdGuard + "\n" + Facts);

        var receipt = Assert.Single(Receipts(output));
        Assert.Equal("skipped", receipt.GetProperty("status").GetString());
        Assert.Equal("target cache writer guard is busy", receipt.GetProperty("reason").GetString());
        Assert.Contains("same_mtime=202001020304", output, StringComparison.Ordinal);
    }

    [Fact]
    public void AllCoversLinkedWorktreesAndNeverTheDonor()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();

        var output = Run(fixture, Fixture + "\n" + Dedupe("--root main --all"));

        var receipt = Assert.Single(Receipts(output));
        Assert.EndsWith("/wt", receipt.GetProperty("root").GetString(), StringComparison.Ordinal);
        Assert.Equal(1, receipt.GetProperty("files_relinked").GetInt32());
    }

    [Fact]
    public void PostBuildScopeSkipsOlderFilesAndDependencyPackages()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();
        const string packages = """
            mkdir -p main/.lake/packages/dep wt/.lake/packages/dep
            fill dep > main/.lake/packages/dep/Dep.olean
            cp main/.lake/packages/dep/Dep.olean wt/.lake/packages/dep/Dep.olean
            """;

        var output = Run(fixture, Fixture + "\n" + packages + "\n"
            + Dedupe("--root wt --since 4102444800") + "\n"
            + Dedupe("--root wt --since 1577836800 --build-only") + "\n"
            + Dedupe("--root wt"));

        var receipts = Receipts(output);
        Assert.Equal(3, receipts.Length);
        Assert.Equal(0, receipts[0].GetProperty("files_relinked").GetInt32());
        Assert.Equal(0, receipts[0].GetProperty("files_differ").GetInt32());
        Assert.Equal(1, receipts[1].GetProperty("files_relinked").GetInt32());
        Assert.Equal(1, receipts[1].GetProperty("files_differ").GetInt32());
        Assert.Equal(1, receipts[2].GetProperty("files_relinked").GetInt32());
        Assert.Equal(1, receipts[2].GetProperty("files_already_shared").GetInt32());
    }

    [Fact]
    public void MissingTargetLakeIsSkipped()
    {
        if (!OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();

        var output = Run(fixture, Fixture + "\nrm -rf wt/.lake\n" + Dedupe("--root wt"));

        var receipt = Assert.Single(Receipts(output));
        Assert.Equal("skipped", receipt.GetProperty("status").GetString());
        Assert.Equal("target .lake is absent", receipt.GetProperty("reason").GetString());
    }

    [Fact]
    public void OtherPlatformsReportUnsupportedWithoutTouchingFiles()
    {
        if (OperatingSystem.IsWindows() || OperatingSystem.IsMacOS()) return;
        using var fixture = new TemporaryDirectory();

        var output = Run(fixture, Fixture.Replace("touch -t 202001020304 ", "true ", StringComparison.Ordinal)
            + "\n" + Dedupe("--root wt"));

        var receipt = Assert.Single(Receipts(output));
        Assert.Equal("unsupported", receipt.GetProperty("status").GetString());
    }

    private static string Dedupe(string arguments) =>
        $"python3 -B \"$SCRIPT\" {arguments.Replace("wt", "\"$FIXTURE/wt\"", StringComparison.Ordinal).Replace("main", "\"$FIXTURE/main\"", StringComparison.Ordinal)}";

    private static string Run(TemporaryDirectory fixture, string body)
    {
        var script = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_cache_dedupe.py");
        var process = TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "export FIXTURE=\"$1\" SCRIPT=\"$2\" HOME=\"$1/home\"\n" + body, "lean-cache-dedupe-test", fixture.Path, script],
            fixture.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        var output = Encoding.UTF8.GetString(process.StandardOutput);
        Assert.True(process.ExitCode == 0, output + Encoding.UTF8.GetString(process.StandardError));
        return output;
    }

    private static JsonElement[] Receipts(string output) => output
        .Split('\n')
        .Where(line => line.StartsWith("LEAN_CACHE_DEDUPE ", StringComparison.Ordinal))
        .Select(line => JsonDocument.Parse(line["LEAN_CACHE_DEDUPE ".Length..]).RootElement.Clone())
        .ToArray();
}
