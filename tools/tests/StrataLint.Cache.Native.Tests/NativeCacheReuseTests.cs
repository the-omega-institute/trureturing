using System.Security.Cryptography;
using StrataLint.TestSupport;
using Xunit;
using FactAttribute = Xunit.SkippableFactAttribute;
using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.Cache.Native.Tests;

public sealed class NativeCacheReuseTests
{
    [Fact]
    public void MissingTransientSetupFilesDoNotInvalidateCompiledModules()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var toolchain = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "lean-toolchain")).Trim();
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), toolchain + "\n");
        File.WriteAllText(Path.Combine(root, "lakefile.toml"), """
            name = "cacheFixture"
            defaultTargets = ["Fixture"]
            [[lean_lib]]
            name = "Fixture"
            """);
        Directory.CreateDirectory(Path.Combine(root, "Fixture"));
        File.WriteAllText(Path.Combine(root, "Fixture/Dependency.lean"), "def fixtureValue : Nat := 3\n");
        File.WriteAllText(Path.Combine(root, "Fixture.lean"), "import Fixture.Dependency\ntheorem fixture_result : fixtureValue = 3 := rfl\n");
        Build();

        var artifacts = Directory.GetFiles(Path.Combine(root, ".lake/build/lib"), "*.olean", SearchOption.AllDirectories)
            .ToDictionary(path => path, path => Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))), StringComparer.Ordinal);
        Assert.Equal(2, artifacts.Count);
        var setup = Directory.GetFiles(Path.Combine(root, ".lake/build/ir"), "*.setup.json", SearchOption.AllDirectories);
        Assert.Equal(2, setup.Length);
        foreach (var path in setup) File.Delete(path);

        // Lake must accept the restored artifacts without permission to compile.
        Build("--no-build");
        foreach (var (path, hash) in artifacts)
            Assert.Equal(hash, Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path))));

        void Build(params string[] options)
        {
            var result = EngineeringProcess.Process(root, "elan", ["run", toolchain, "lake", "build", .. options],
                hangGuard: TestBudgets.LongWorkflowProcessHangGuard, maximumOutputBytes: 1024 * 1024);
            Assert.True(result.Exit == 0,
                result.Text);
        }
    }
}
