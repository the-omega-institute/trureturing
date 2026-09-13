using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using TemporaryFile = StrataLint.TestSupport.TemporaryFileSystem.File;
using TemporaryDirectoryIo = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

// The declaration report is a local source-bound fixture. The real pair entry,
// input verifier, demand loop, current compiler and strict admission all execute.
// Reuse the existing compiler adapter so the fixture never builds a base judge.
internal sealed class PairSourcePreparationFixture
{
    private readonly string scratch;
    private readonly string root;
    private readonly string compiler = TestRepositoryLayout.FindRoot();

    internal PairSourcePreparationFixture(string scratch, string root)
    {
        this.scratch = scratch;
        this.root = root;
        LeanReportInputScriptTests.CopyBatchProducerInputs(root);
        Write("Trureturing.lean", "import D5.S0.Carrier.Anonymous\n");
        Write("tools/lean-inspector/inspect.sh", ReportProducer);
        Write("tools/lean-inspector/source-context.sh", ContextProducer);
        Write("tools/scripts/worktree/lean-cache-ensure.sh", "#!/usr/bin/env bash\nset -euo pipefail\n");
        TemporaryFile.WriteAllText(Path.Combine(scratch, "prepare.py"), QualifiedSourceContextScripts.Preparation);
        Run("chmod", ["+x", Path.Combine(root, "tools/lean-inspector/inspect.sh")]);
    }

    internal void Prepare(string report, string? baseline, bool demanded)
    {
        var protectedParent = new StrataLint.Cli.GitRepositoryGateway(root).Prepare("HEAD^1").Revision;
        Produce("produced");
        if (baseline is not null) return;
        var bytes = TemporaryFile.ReadAllBytes(report + ".source-context.json");
        // An existing report cache can predate the sibling. The next environment-base
        // invocation must rebuild demanded context without rebuilding the report.
        foreach (var path in TemporaryDirectoryIo.EnumerateFiles(Path.Combine(scratch, "cache"),
            "*.source-context.json", SearchOption.AllDirectories)) TemporaryFile.Delete(path);
        Produce("cached");
        Assert.Equal(bytes, TemporaryFile.ReadAllBytes(report + ".source-context.json"));
        if (!demanded) return;

        // An explicitly invalid BASE must never fall back to the first parent.
        var invalid = Invoke(new string('0', 40));
        Assert.NotEqual(0, invalid.ExitCode);
        Assert.Equal(bytes, TemporaryFile.ReadAllBytes(report + ".source-context.json"));

        void Produce(string mode)
        {
            var run = Invoke(baseline);
            var stdout = Encoding.UTF8.GetString(run.StandardOutput);
            Assert.True(run.ExitCode == 0, stdout + Encoding.UTF8.GetString(run.StandardError));
            Assert.Contains("LEAN_REPORT_PROVENANCE side=candidate mode=" + mode, stdout, StringComparison.Ordinal);
            var receipt = stdout.Split('\n').Single(line => line.StartsWith("LEAN_SOURCE_CONTEXT ", StringComparison.Ordinal));
            using var metrics = JsonDocument.Parse(receipt["LEAN_SOURCE_CONTEXT ".Length..]);
            Console.WriteLine($"PAIR_SOURCE_CONTEXT explicit_base={baseline is not null} demanded={demanded} mode={mode} {receipt}");
            if (!demanded)
            {
                Assert.Equal(0, metrics.RootElement.GetProperty("consumer_requests").GetInt32());
                Assert.Equal(0, metrics.RootElement.GetProperty("queries").GetInt32());
                Assert.Equal(0, metrics.RootElement.GetProperty("compiler_modules").GetInt32());
            }
            Assert.Equal(0, metrics.RootElement.GetProperty("external_bytes").GetInt32());
        }

        ProcessOutput Invoke(string? sourceBase) => TestProcessRunner.Run("env", [
            $"STRATALINT_SOURCE_BASE={(sourceBase is null ? protectedParent : string.Empty)}",
            $"STRATALINT_REPORT_CACHE_ROOT={Path.Combine(scratch, "cache")}",
            $"STRATALINT_SUPERVISOR_ROOT={Path.Combine(scratch, "supervisor")}",
            $"PAIR_COMPILER={compiler}", $"PAIR_PREPARATION={Path.Combine(scratch, "prepare.py")}",
            $"PAIR_REPORT={report}",
            "bash", Path.Combine(compiler, "tools/scripts/lean-report-pair.sh"),
            "--producer", Path.Combine(root, "tools/lean-inspector/inspect.sh"),
            "--lake-bin", "/usr/bin/true", "--candidate-root", root, "--candidate-output", report,
            .. sourceBase is null ? Array.Empty<string>() : ["--base", sourceBase]],
            scratch, BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
    }

    private void Write(string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        TemporaryDirectoryIo.CreateDirectory(Path.GetDirectoryName(path)!);
        TemporaryFile.WriteAllText(path, contents);
    }

    private void Run(string executable, string[] arguments)
    {
        var result = TestProcessRunner.Run(executable, arguments, scratch,
            BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
    }

    private const string ContextProducer = """
        #!/usr/bin/env bash
        set -euo pipefail
        mode="$1"
        shift
        repository=""
        report=""
        base=""
        while [[ $# -gt 0 ]]; do
          case "$1" in
            --repository) repository="$2"; shift 2 ;;
            --report) report="$2"; shift 2 ;;
            --base) base="$2"; shift 2 ;;
            --lake) shift 2 ;;
            *) exit 2 ;;
          esac
        done
        [[ "$mode" != verify ]] || mode=offline
        exec python3 "$PAIR_PREPARATION" "$PAIR_COMPILER" "$repository" "$report" "$base" "$mode"
        """;

    private const string ReportProducer = """
        #!/usr/bin/env bash
        set -euo pipefail
        output=""
        while [[ $# -gt 0 ]]; do
          case "$1" in
            --repository) shift 2 ;;
            --output) output="$2"; shift 2 ;;
            *) exit 2 ;;
          esac
        done
        cp "$PAIR_REPORT" "$output"
        cp "${PAIR_REPORT}.materials.zip" "${output}.materials.zip"
        hash="$(openssl dgst -sha256 "$output" | awk '{print $NF}')"
        printf '%s  %s\n' "$hash" "$(basename "$output")" > "${output}.sha256"
        mkdir -p "${output}.logs"
        printf '%s\n' 'local declaration fixture' > "${output}.logs/producer.log"
        """;
}
