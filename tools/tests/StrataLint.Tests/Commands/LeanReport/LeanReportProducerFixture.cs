using FixtureDirectory = StrataLint.TestSupport.TemporaryFileSystem.Directory;
using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal static class LeanReportProducerFixture
{
    internal static void SeedReachableScripts(string repository)
    {
        // Leaf stubs cover the producer script closure; keep each test's installed behavior.
        foreach (var relative in new[]
        {
            "tools/lean-inspector/inspect.sh",
            "tools/scripts/lean-report-pair.sh",
            "tools/scripts/lib/resource-observation-lib.sh",
            "tools/scripts/lib/segment-evidence-lib.sh",
            "tools/scripts/report/lean-report-bundle-lib.sh",
            "tools/scripts/report/lean-report-ci-baseline.sh",
            "tools/scripts/report/lean-report-input.sh",
            "tools/scripts/report/report-supervisor.sh",
            "tools/scripts/workflow/install-lean-toolchain.sh",
            "tools/scripts/workflow/judge-content-address.sh",
            "tools/scripts/workflow/scribe-content-checks.sh",
            "tools/scripts/workflow/segment-lean-inspect.sh",
            "tools/scripts/worktree/lean-cache-ensure.sh",
            "tools/scripts/worktree/lean-cache-publish.sh",
            "tools/scripts/worktree/lean-cache-run.sh",
        })
        {
            var path = Path.Combine(repository, relative);
            if (FixtureFile.Exists(path)) continue;
            FixtureDirectory.CreateDirectory(Path.GetDirectoryName(path)!);
            FixtureFile.WriteAllText(path, "#!/usr/bin/env bash\n");
        }
    }
}
