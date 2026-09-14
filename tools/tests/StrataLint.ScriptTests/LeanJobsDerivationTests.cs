using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed class LeanJobsDerivationTests
{
    // Fixed fixture inputs at the production receipt's quotient boundaries.
    private const long Reserve = 2147483648;
    private const long Peak = 6110000000;
    private const string Script = "tools/scripts/worktree/lean-cache-run.sh";

    [Theory]
    [InlineData(8, Reserve + 2 * Peak - 1, 1)]
    [InlineData(8, Reserve + 2 * Peak, 2)]
    [InlineData(8, Reserve + 2 * Peak + 1, 2)]
    [InlineData(8, Reserve + 3 * Peak, 3)]
    [InlineData(1, Reserve + 3 * Peak, 1)]
    [InlineData(2, Reserve + 3 * Peak, 2)]
    [InlineData(3, Reserve + 3 * Peak, 3)]
    public void AdjacentCapacityBoundariesChangeTheEffectiveJobCount(int cores, long memory, int jobs)
    {
        if (OperatingSystem.IsWindows()) return;
        var result = Derive(cores.ToString(), memory.ToString());
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(Receipt(cores, memory, cores, (memory - Reserve) / Peak, jobs), result.StandardOutput.Trim());
    }

    [Theory]
    [InlineData(Reserve - 1, -1)]
    [InlineData(Reserve, 0)]
    [InlineData(Reserve + Peak - 1, 0)]
    public void InsufficientMemoryFailsClosedWithoutClamping(long memory, int quotient)
    {
        if (OperatingSystem.IsWindows()) return;
        var result = Derive("8", memory.ToString());
        Assert.Equal(1, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains($"LEAN_JOBS_CAPACITY_INSUFFICIENT cores=8 mem_total_bytes={memory}", result.StandardError);
        Assert.Contains($"q_mem={quotient} jobs={quotient}", result.StandardError);
    }

    [Theory]
    [InlineData("250000 100000", "max", 2, Reserve + 8 * Peak, 8, 2)]
    [InlineData("max 100000", "14367483648", 8, Reserve + 2 * Peak, 2, 2)]
    [InlineData("300000 100000\n150000 100000", "max\n14367483648", 1, Reserve + 2 * Peak, 2, 1)]
    [InlineData("1600000 100000", "999999999999", 8, Reserve + 8 * Peak, 8, 8)]
    [InlineData("max 100000", "max", 8, Reserve + 8 * Peak, 8, 8)]
    public void CgroupBoundsIncludeAncestorsAndNeverIncreaseHostCapacity(
        string cpu, string memory, int qCpu, long effectiveMemory, int qMem, int jobs)
    {
        if (OperatingSystem.IsWindows()) return;
        var result = Derive("8", (Reserve + 8 * Peak).ToString(), cpu, memory);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(Receipt(8, effectiveMemory, qCpu, qMem, jobs, cpu, memory, Reserve + 8 * Peak), result.StandardOutput.Trim());
    }

    [Theory]
    [InlineData("99999 100000", "max", "q_cpu=0")]
    [InlineData("max 100000", "0", "q_mem=-1")]
    public void CgroupBelowOneJobFailsClosed(string cpu, string memory, string quotient)
    {
        if (OperatingSystem.IsWindows()) return;
        var result = Derive("8", (Reserve + 8 * Peak).ToString(), cpu, memory);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains("LEAN_JOBS_CAPACITY_INSUFFICIENT", result.StandardError);
        Assert.Contains(quotient, result.StandardError);
        Assert.Empty(result.StandardOutput);
    }

    [Theory]
    [InlineData("0", "10000000000", "", "")]
    [InlineData("8", "unknown", "", "")]
    [InlineData("8", "10000000000", "max 0", "")]
    [InlineData("8", "10000000000", "broken", "")]
    [InlineData("8", "10000000000", "", "-1")]
    public void MalformedCapacityIsDiagnosed(string cores, string memory, string cpu, string cgroupMemory)
    {
        if (OperatingSystem.IsWindows()) return;
        var result = Derive(cores, memory, cpu, cgroupMemory);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains("LEAN_JOBS_CAPACITY_INVALID", result.StandardError);
        Assert.Empty(result.StandardOutput);
    }

    [Theory]
    [InlineData("lake", Reserve + 2 * Peak, "build", 97, "2")]
    [InlineData("/fixture/bin/lake", Reserve + 2 * Peak, "build", 97, "2")]
    [InlineData("/fixture/bin/lake-wrapper", Reserve + 2 * Peak, "build", 97, "2")]
    [InlineData("/fixture/bin/lake-wrapper", Reserve, "build", 1, null)]
    [InlineData("lake", Reserve, "build", 1, null)]
    [InlineData("lake", Reserve, "env", 97, "999")]
    public void AdapterAppliesDerivedEnvironmentAndPreservesWriterAndArguments(
        string command, long memory, string verb, int exitCode, string? threads)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        var script = Path.Combine(fixture.Path, Script);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), Script), script);
        var result = Run(fixture.Path,
            """
            source "$1"
            original="$(declare -f lean_jobs_derive)"
            eval "${original/lean_jobs_derive/fixture_derive}"
            lean_jobs_derive() { fixture_derive 8 "$FIXTURE_MEMORY" '' ''; }
            dotnet() { printf 'threads=%s\n' "$LEAN_NUM_THREADS"; printf '<%s>\n' "$@"; return 97; }
            export -f dotnet
            # 'exec dotnet' uses this executable stub, preserving the real adapter.
            mkdir "$2/bin"
            printf '#!/bin/bash\ndotnet "$@"\n' > "$2/bin/dotnet"
            chmod +x "$2/bin/dotnet"
            export PATH="$2/bin:$PATH" LEAN_NUM_THREADS=999
            FIXTURE_MEMORY="$3"
            lean_cache_run "$4" "$5" 'target with spaces'
            """, script, fixture.Path, memory.ToString(), command, verb);
        Assert.Equal(exitCode, result.ExitCode);
        if (threads is null)
        {
            Assert.Empty(result.StandardOutput);
            Assert.Contains("LEAN_JOBS_CAPACITY_INSUFFICIENT", result.StandardError);
        }
        else
        {
            Assert.Contains($"threads={threads}\n", result.StandardOutput);
            Assert.Contains($"<worktree>\n<with-cache-writer>\n<-->\n<{command}>\n<{verb}>\n<target with spaces>", result.StandardOutput);
            if (verb == "build")
                Assert.Equal(Receipt(8, memory, 8, 2, 2), result.StandardError.Trim());
            else
                Assert.Empty(result.StandardError);
        }
    }

    [Theory]
    [InlineData("memory.max", true)]
    [InlineData("memory.max", false)]
    [InlineData("cpu.max", true)]
    [InlineData("cpu.max", false)]
    public void EveryVisibleCgroupMountContributesLimits(string limitedResource, bool narrowFirst)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        var result = Run(fixture.Path,
            """
            python3 - "$@" <<'PY'
            import ast
            from pathlib import Path
            import sys
            source = Path(sys.argv[1]).read_text().split("<<'PY'\n", 1)[1].split('\nPY\n', 1)[0]
            tree = ast.parse(source)
            tree.body = [node for node in tree.body if not isinstance(node, ast.Try)]
            ns = {}
            exec(compile(tree, sys.argv[1], 'exec'), ns)
            root = Path(sys.argv[2])
            proc, narrow, broad = root / 'proc', root / 'narrow', root / 'broad'
            (proc / 'self').mkdir(parents=True)
            (proc / 'self/cgroup').write_text('0::/parent/child/leaf\n')
            for directory in [narrow, narrow / 'leaf', broad, broad / 'parent',
                              broad / 'parent/child', broad / 'parent/child/leaf']:
                directory.mkdir(parents=True, exist_ok=True)
                (directory / 'cpu.max').write_text('max 100000\n')
                (directory / 'memory.max').write_text('max\n')
            limit = '8257483648' if sys.argv[3] == 'memory.max' else '100000 100000'
            (broad / 'parent' / sys.argv[3]).write_text(limit + '\n')
            mounts = [f'30 20 0:28 /parent/child {narrow} rw - cgroup2 cgroup rw\n',
                      f'31 20 0:28 / {broad} rw - cgroup2 cgroup rw\n']
            if sys.argv[4] == 'False':
                mounts.reverse()
            (proc / 'self/mountinfo').write_text(''.join(mounts))
            sys.exit(ns['derive']('8', '51027483648', *ns['cgroup_limits'](proc)))
            PY
            """, Path.Combine(TestRepositoryLayout.FindRoot(), Script), fixture.Path,
            limitedResource, narrowFirst.ToString());
        Assert.Equal(0, result.ExitCode);
        Assert.EndsWith("jobs=1", result.StandardOutput.Trim());
        Assert.Contains("cgroup_sources=", result.StandardOutput);
        Assert.Contains("/narrow/", result.StandardOutput);
        Assert.Contains("/broad/parent/" + limitedResource, result.StandardOutput);
    }

    [Theory]
    [InlineData(Reserve + 2 * Peak, 97)]
    [InlineData(Reserve, 1)]
    public void CanonicalReportForwardsAlternateLakeBuildThroughCapacityGuard(long memory, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        foreach (var relative in new[] { Script, "tools/scripts/report/lean-report.sh", "tools/lean-inspector/inspect.sh" })
        {
            var destination = Path.Combine(fixture.Path, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), relative), destination);
        }
        var result = Run(fixture.Path,
            """
            mkdir -p bin tools/scripts/lib
            real_python="$(command -v python3)"
            export FIXTURE_MEMORY="$1" FIXTURE_PYTHON="$real_python"
            cat > bin/python3 <<'SH'
            #!/bin/bash
            exec "$FIXTURE_PYTHON" - 8 "$FIXTURE_MEMORY" '' ''
            SH
            cat > bin/dotnet <<'SH'
            #!/bin/bash
            printf 'threads=%s\n' "$LEAN_NUM_THREADS"
            printf '<%s>\n' "$@"
            exit 97
            SH
            printf '#!/bin/bash\nexit 98\n' > bin/lake-wrapper
            # The pair boundary is stubbed; both canonical entry scripts and
            # the capacity adapter run unchanged. Stop at writer dispatch.
            cat > tools/scripts/lean-report-pair.sh <<'SH'
            #!/bin/bash
            [[ "$1" == --producer && "$3" == --lake-bin && "$5" == --candidate-root && "$7" == --candidate-output ]] || exit 99
            export LAKE_BIN="$4"
            exec /bin/bash "$2" --repository "$6" --output "$8"
            SH
            cat > tools/scripts/report/lean-report-input.sh <<'SH'
            #!/bin/bash
            digest=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
            if [[ "$1" == compatibility-token ]]; then
              printf '%s\n' "$digest"
            else
              printf '%s %s %s %s\n' "$digest" "$digest" "$digest" "$digest"
            fi
            SH
            printf 'resource_observe() { :; }\n' > tools/scripts/lib/resource-observation-lib.sh
            touch tools/lean-inspector/Inspector.lean
            chmod +x bin/* tools/scripts/lean-report-pair.sh tools/scripts/report/lean-report-input.sh tools/scripts/worktree/lean-cache-run.sh
            export PATH="$PWD/bin:$PATH" LAKE_BIN="$PWD/bin/lake-wrapper" LEAN_NUM_THREADS=999 CI=true
            /bin/bash tools/scripts/report/lean-report.sh
            """, memory.ToString());
        Assert.Equal(expectedExit, result.ExitCode);
        // inspect.sh replays failed phase output to stderr, including the
        // diagnostic exit from the writer stub in the sufficient case.
        Assert.Contains("LEAN_INSPECTOR_FAILED phase=build", result.StandardError);
        if (expectedExit == 97)
        {
            Assert.Contains("threads=2", result.StandardError);
            Assert.Contains("<worktree>\n<with-cache-writer>\n<-->\n", result.StandardError);
            Assert.Contains("/bin/lake-wrapper>\n<build>", result.StandardError);
            Assert.Contains("LEAN_JOBS_DERIVATION", result.StandardError);
        }
        else
        {
            Assert.Contains("LEAN_JOBS_CAPACITY_INSUFFICIENT", result.StandardError);
            Assert.DoesNotContain("<with-cache-writer>", result.StandardError);
        }
    }

    private static string Receipt(int cores, long memory, int qCpu, long qMem, int jobs,
        string cpu = "", string cgroupMemory = "", long? hostMemory = null) =>
        $"LEAN_JOBS_DERIVATION cores={cores} mem_total_bytes={memory} host_mem_total_bytes={hostMemory ?? memory} "
        + $"reserve_bytes={Reserve} per_process_bytes={Peak} "
        + "r_cpu_cores=1 r_cpu_basis=ASSUMED-UNVERIFIED:ARCH-03 "
        + $"cpu_max={JsonSerializer.Serialize(cpu.Split('\n', StringSplitOptions.RemoveEmptyEntries))} "
        + $"memory_max={JsonSerializer.Serialize(cgroupMemory.Split('\n', StringSplitOptions.RemoveEmptyEntries))} "
        + $"cgroup_sources=[\"injected\"] q_cpu={qCpu} q_mem={qMem} jobs={jobs}";

    private static (int ExitCode, string StandardOutput, string StandardError) Derive(
        string cores, string memory, string cpu = "", string cgroupMemory = "") =>
        Run(TestRepositoryLayout.FindRoot(), "source \"$1\"; shift; lean_jobs_derive \"$@\"",
            Path.Combine(TestRepositoryLayout.FindRoot(), Script), cores, memory, cpu, cgroupMemory);

    private static (int ExitCode, string StandardOutput, string StandardError) Run(
        string cwd, string body, params string[] arguments)
    {
        var result = TestProcessRunner.Run("/bin/bash", ["-c", body, "lean-jobs-test", .. arguments],
            cwd, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        return (result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput), Encoding.UTF8.GetString(result.StandardError));
    }
}
