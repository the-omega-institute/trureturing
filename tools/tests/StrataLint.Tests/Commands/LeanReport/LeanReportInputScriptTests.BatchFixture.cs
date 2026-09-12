using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    internal static ProcessOutput RunWithBuiltInputCli(
        IReadOnlyList<string> arguments, string workingDirectory, TimeSpan hangGuard) =>
        TestProcessRunner.Run("/bin/bash",
            ["-c", """
                set -euo pipefail
                # The test project's CLI reference is built by the canonical test build.
                # Reuse only that immutable program; every selector still reads this invocation's inputs.
                export BATCH_NATIVE_CLI="$1"
                shift
                dotnet() {
                  if [[ "${1:-}" == run && " $* " == *' -- filemap-conform --input-scopes '* ]]; then
                    while [[ "$1" != -- ]]; do shift; done
                    shift
                    command dotnet "$BATCH_NATIVE_CLI" "$@"
                  else
                    command dotnet "$@"
                  fi
                }
                export -f dotnet
                exec "$@"
                """, "lean-input-fixture", Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"),
                .. arguments], workingDirectory, hangGuard, 1024 * 1024);

    internal static void CopyBatchProducerInputs(string root)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.CopyBatchInputs(root);
    }

    internal static void AttestBatchReport(string root, string report)
    {
        var result = RunWithBuiltInputCli(
            ["/bin/bash", Path.Combine(root, InputHelperPath), "address", "--repository", root],
            root, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var fields = Fields(result);
        var hash = Convert.ToHexStringLower(SHA256.HashData(TemporaryFileSystem.File.ReadAllBytes(report)));
        TemporaryFileSystem.File.WriteAllText(report + ".sha256", $"{hash}  {Path.GetFileName(report)}\n");
        TemporaryFileSystem.File.WriteAllText(report + ".provenance.json", "{}\n");
        TemporaryFileSystem.File.WriteAllText(report + ".source-context.json",
            "{\"schema\":\"lean-source-context/1\",\"files\":[],\"registrations\":[]}\n");
        TemporaryFileSystem.File.WriteAllText(report + ".input.attestation",
            "schema=stratalint-lean-report-input-attestation-v1\n"
            + $"repository_input_sha256={fields[0]}\nproducer_sha256={fields[1]}\nreport_sha256={hash}\n");
    }

    private sealed partial class LeanReportInputFixture
    {
        internal void CopyBatchInputs(string root)
        {
            foreach (var path in TemporaryFileSystem.Directory.EnumerateFiles(repository, "*", SearchOption.AllDirectories))
            {
                var relative = Path.GetRelativePath(repository, path).Replace('\\', '/');
                if (relative.StartsWith("D5/", StringComparison.Ordinal)
                    || relative.StartsWith("Blueprint/", StringComparison.Ordinal)
                    || relative == "Trureturing.lean") continue;
                var destination = Path.Combine(root, relative);
                if (TemporaryFileSystem.File.Exists(destination))
                {
                    // Preserve the admission fixture's entries while registering the copied producer inputs.
                    if (relative == "Meta/FILEMAP.toml")
                        TemporaryFileSystem.File.AppendAllText(destination, "\n" + Registration + "\n");
                    continue;
                }
                TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                TemporaryFileSystem.File.WriteAllBytes(destination, TemporaryFileSystem.File.ReadAllBytes(path));
            }
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, InputHelperPath),
                "#!/bin/bash\nexec /bin/bash '"
                + Path.Combine(TestRepositoryLayout.FindRoot(), InputHelperPath) + "' \"$@\"\n");
        }
    }
}
