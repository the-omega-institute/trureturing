using StrataLint.Scribe;
using Xunit;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class DependencyDirectionTests
{
    [Fact]
    public void DocumentsOwnsANamespacedEntryPointAndCanReachScribeCommands()
    {
        Assert.Equal("StrataLint.Scribe.Documents.Program", typeof(Program).FullName);
        Assert.Contains("routing-probe-must-be-absent", ScribeCli.ImplementedCommands);
    }
}
