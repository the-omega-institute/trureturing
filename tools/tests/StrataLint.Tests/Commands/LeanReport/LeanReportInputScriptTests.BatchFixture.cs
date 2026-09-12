using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanReportInputScriptTests
{
    internal static void CopyBatchProducerInputs(string root)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.CopyBatchInputs(root);
    }

    internal static void AttestBatchReport(string root, string report)
    {
        var result = TestProcessRunner.Run("/bin/bash",
            ["-c", """
                # The canonical build supplies the CLI; bootstrap still selects and hashes real inputs.
                export BATCH_NATIVE_CLI="$1"
                dotnet() {
                  [[ "$1" == run ]] || return 2
                  while [[ $# -gt 0 && "$1" != -- ]]; do shift; done
                  [[ $# -gt 0 ]] || return 2
                  shift
                  command dotnet "$BATCH_NATIVE_CLI" "$@"
                }
                export -f dotnet
                exec /bin/bash "$2" address --repository "$3"
                """, "batch-report-input", Path.Combine(AppContext.BaseDirectory, "StrataLint.dll"),
                Path.Combine(root, InputHelperPath), root], root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
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
