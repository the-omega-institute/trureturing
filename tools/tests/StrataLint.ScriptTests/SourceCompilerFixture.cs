using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[CollectionDefinition("Current source compiler", DisableParallelization = true)]
public sealed class SourceCompilerCollection : ICollectionFixture<SourceCompilerFixture> { }

// These tests share the current checkout's canonical cache writer. Prepare it
// once per collection, then execute only run-local compiler queries and fixtures.
public sealed class SourceCompilerFixture
{
    public string Root { get; } = TestRepositoryLayout.FindRoot();

    public SourceCompilerFixture()
    {
        var ensure = TestProcessRunner.Run("make", ["lean-cache-ensure"], Root,
            BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        Assert.True(ensure.ExitCode == 0, Encoding.UTF8.GetString(ensure.StandardOutput) + Encoding.UTF8.GetString(ensure.StandardError));
    }
}
