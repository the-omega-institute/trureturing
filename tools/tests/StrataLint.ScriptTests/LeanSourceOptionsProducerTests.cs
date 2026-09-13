using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Current source compiler")]
public sealed class LeanSourceOptionsProducerTests(SourceCompilerFixture compiler)
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentLakeOwnsPackageAndLibraryOptionOverrides(bool leanConfiguration)
    {
        using var temporary = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(temporary.Path, leanConfiguration ? "lakefile.lean" : "lakefile.toml"),
            leanConfiguration ? """
                import Lake
                open Lake DSL
                package contextOptions where
                  leanOptions := #[⟨`maxRecDepth, 111⟩]
                lean_lib Fixture where
                  leanOptions := #[⟨`maxRecDepth, 222⟩, ⟨`pp.unicode.fun, false⟩]
                  moreLeanArgs := #["-DmaxHeartbeats=333"]
                """ : """
                name = "contextOptions"
                [leanOptions]
                maxRecDepth = 111
                [[lean_lib]]
                name = "Fixture"
                moreLeanArgs = ["-DmaxHeartbeats=333"]
                [lean_lib.leanOptions]
                maxRecDepth = 222
                pp.unicode.fun = false
                """);
        File.WriteAllText(Path.Combine(temporary.Path, "Fixture.lean"), "import Init\n");
        var root = compiler.Root;
        var run = TestProcessRunner.Run("python3", [
            "-c", SourceContextContractScript.Source, root,
            "--options", temporary.Path, "Fixture"], root,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(run.ExitCode == 0, Encoding.UTF8.GetString(run.StandardOutput) + Encoding.UTF8.GetString(run.StandardError));
        using var json = JsonDocument.Parse(run.StandardOutput);
        Assert.Equal(222, json.RootElement.GetProperty("options").GetProperty("maxRecDepth").GetInt32());
        Assert.False(json.RootElement.GetProperty("options").GetProperty("pp.unicode.fun").GetBoolean());
        Assert.Contains(json.RootElement.GetProperty("flags").EnumerateArray(),
            flag => flag.GetString() == "-DmaxHeartbeats=333");
    }
}
