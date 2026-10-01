using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.TestEvidence;

internal sealed record CompilationProofResult(int ExitCode, string Output, string Error);

internal static class CompileProofCommand
{
    internal static CompilationProofResult Run(IReadOnlyList<string> arguments, string repositoryRoot)
    {
        var output = new StringBuilder();
        try
        {
            if (arguments.Count != 1 || arguments[0] is not ("capability-proof" or "banned-api-proof"))
                throw new ArgumentException("USAGE: StrataLint compile-proof capability-proof|banned-api-proof");
            var proof = arguments[0];
            var project = proof == "capability-proof" ? "tools/tests/CompileFailProof/CompileFailProof.csproj"
                : "tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj";
            var source = proof == "banned-api-proof"
                ? File.ReadAllText(Path.Combine(repositoryRoot, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs")) : null;
            var restore = Capture(["restore", project, "--locked-mode", "-nr:false"]);
            if (restore.ExitCode != 0) return new(2, output.ToString(), "INFRASTRUCTURE_FAILURE compile-proof restore failed\n");
            var build = Capture(["build", project, "--no-restore", "--no-dependencies", "--configuration", "Release", "-nr:false"]);
            var text = Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError);
            if (build.ExitCode is not (0 or 1)) return new(2, output.ToString(), "INFRASTRUCTURE_FAILURE compile-proof build failed\n");
            var matched = proof == "capability-proof" ? CompilationProof.ValidateCapability(build.ExitCode, text)
                : CompilationProof.ValidateBannedApi(build.ExitCode, text, source!);
            if (!matched) return new(1, output.ToString(), "COMPILATION_PROOF_FAILED " + proof + "\n");
            output.Append("EXPECTED_DIAGNOSTIC ").Append(JsonSerializer.Serialize(new
            {
                proof, diagnostic = proof == "capability-proof" ? "CS7036" : "RS0030", status = "matched", raw_exit = build.ExitCode,
            })).Append('\n');
            return new(0, output.ToString(), "");
        }
        catch (Exception exception)
        {
            return new(2, output.ToString(), "INFRASTRUCTURE_FAILURE compile-proof: " + exception.Message + "\n");
        }

        ProcessOutput Capture(string[] command)
        {
            var result = BoundedProcessRunner.Run("dotnet", command, repositoryRoot,
                BoundedProcessRunner.HangDetectionBudget, 16 * 1024 * 1024);
            output.Append(Encoding.UTF8.GetString(result.StandardOutput)).Append(Encoding.UTF8.GetString(result.StandardError));
            return result;
        }
    }
}
