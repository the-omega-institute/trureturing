using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeTestMapStoreTests
{
    [Fact]
    public void ResolveDotnetExecutableUsesExplicitHostPath()
    {
        using var temporary = new TemporaryDirectory();
        var host = Path.Combine(temporary.Path, "selected-dotnet");
        TemporaryFileSystem.File.WriteAllText(host, "synthetic host; never executed");
        var original = Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        try
        {
            Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", host);
            Assert.Equal(host, MsBuildCompileOracle.ResolveDotnetExecutable());
        }
        finally
        {
            Environment.SetEnvironmentVariable("DOTNET_HOST_PATH", original);
        }
    }

    [Fact]
    public void QueryUsesEvaluationEnvironment()
    {
        using var temporary = new TemporaryDirectory();
        var expected = MsBuildCompileOracle.EvaluationEnvironment();
        var calls = 0;
        var result = MsBuildCompileOracle.Query(temporary.Path, ["Test.csproj"], "/fake/dotnet",
            run: (host, arguments, directory, timeout, maximumOutputBytes, standardInput, environment) =>
            {
                calls++;
                Assert.Equal("/fake/dotnet", host);
                Assert.Equal(temporary.Path, directory);
                Assert.Contains("-getItem:Compile", arguments);
                Assert.NotNull(environment);
                Assert.Equal(expected, environment);
                return new ProcessOutput(0, "{\"Items\":{\"Compile\":[]}}"u8.ToArray(), []);
            });

        Assert.Equal(1, calls);
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void EvaluationEnvironmentIsAllowlistedOrderedAndImmutable()
    {
        var expected = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var name in new[] { "PATH", "HOME", "TMPDIR", "TMP", "TEMP", "DOTNET_ROOT",
                     "DOTNET_HOST_PATH", "NUGET_PACKAGES", "LANG", "LC_ALL" })
        {
            if (Environment.GetEnvironmentVariable(name) is { } value) expected.Add(name, value);
        }
        expected.Add("DOTNET_CLI_TELEMETRY_OPTOUT", "1");
        expected.Add("DOTNET_NOLOGO", "1");
        expected.Add("DOTNET_SKIP_FIRST_TIME_EXPERIENCE", "1");

        var actual = MsBuildCompileOracle.EvaluationEnvironment();

        Assert.Equal(expected.ToArray(), actual.ToArray());
        Assert.IsAssignableFrom<System.Collections.Immutable.IImmutableDictionary<string, string>>(actual);
    }

}
