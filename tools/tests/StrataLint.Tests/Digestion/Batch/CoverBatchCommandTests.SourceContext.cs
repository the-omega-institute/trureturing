using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverBatchCommandTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void FinalEmissionValidatesCapturedSourceContextWithProtectedBase(bool complete)
    {
        using var world = new BatchWorld { UseGitReader = true };
        WriteEmissionInputs(world.Root);
        // The canonical bundle verifier calls the source verifier with the batch's
        // protected base and the captured sibling, after coverage is committed.
        WriteScribeFixture(world.Root, "tools/lean-inspector/source-context.sh", """
            #!/usr/bin/env bash
            set -euo pipefail
            test "$1" = verify
            shift
            report=""
            base=""
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --report) report="$2"; shift 2 ;;
                --base) base="$2"; shift 2 ;;
                *) shift ;;
              esac
            done
            test "$base" = baseline
            if [[ ! -f "${report}.source-context.json" ]] || [[ "$(cat "${report}.source-context.json")" != 'captured source input' ]]; then
              echo 'demanded source context is missing or stale' >&2
              exit 2
            fi
            """ + "\n");
        var report = world.WriteReportBundle();
        if (complete) TemporaryFileSystem.File.WriteAllText(report + ".source-context.json", "captured source input\n");
        else TemporaryFileSystem.File.Delete(report + ".source-context.json");
        var calls = 0;
        BatchClaimDefinition.Creating.Value = () =>
        {
            if (++calls == 1)
                TemporaryFileSystem.File.WriteAllText(report + ".source-context.json", "replaced source input\n");
        };
        try
        {
            var result = world.RunProducers(Row(First, Gid) + Row(Second, OtherGid));
            Assert.Equal(complete, result.Success);
            Assert.Equal(["applied", "applied"], Results(result).Select(item => item.Status).ToArray());
            Assert.Single(world.Entry(First).Coverage);
            Assert.Single(world.Entry(Second).Coverage);
            if (!complete) Assert.Contains("demanded source context", result.Error, StringComparison.Ordinal);
            else Assert.NotEmpty(TemporaryFileSystem.File.ReadAllBytes(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
        }
        finally { BatchClaimDefinition.Creating.Value = null; }
    }
}
