using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

[Collection("Lean cold production integration")]
public sealed class CompiledFibIntegrationTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    [Fact]
    public void CompilerArtifactConsumer()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        string[] sources = ["Reg/Support/AuricFibCompiledSource.lean", "Reg/Support/AuricFibCompiledFixture.lean"];
        var config = Path.Combine(root, "tools/lean-inspector-reg/lakefile.toml");
        var configuration = File.ReadAllBytes(config);
        var configMode = File.GetUnixFileMode(config);
        var configMtime = File.GetLastWriteTimeUtc(config);
        var configAtime = File.GetLastAccessTimeUtc(config);
        var ownsSources = sources.All(path => !File.Exists(Path.Combine(root, path)));
        try
        {
            InspectorNativeTestRunner.Run(compiler, "test_auric_fib_compiled.CompiledFibIntegration");
        }
        finally
        {
            // The ordinary supervisor owns the child tree. Restore only this
            // invocation's sources/configuration if Python cleanup was cut off.
            if (ownsSources)
            {
                foreach (var path in sources) File.Delete(Path.Combine(root, path));
                if (!File.ReadAllBytes(config).SequenceEqual(configuration))
                {
                    File.WriteAllBytes(config, configuration);
                    File.SetUnixFileMode(config, configMode);
                    File.SetLastWriteTimeUtc(config, configMtime);
                    File.SetLastAccessTimeUtc(config, configAtime);
                }
            }
        }
    }
}
