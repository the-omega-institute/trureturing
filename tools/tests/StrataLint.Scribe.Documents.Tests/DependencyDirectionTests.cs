using StrataLint.Scribe;
using Xunit;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class DependencyDirectionTests
{
    [Fact]
    public void DocumentsIsALibraryAndScribeOwnsTheCommandEntryPoint()
    {
        Assert.Null(DocumentAssembly.Value.EntryPoint);
        Assert.Equal("StrataLint.Scribe.ScribeProgram", typeof(ScribeProgram).FullName);
        Assert.Contains("emit", ScribeCli.ImplementedCommands);
    }
}
