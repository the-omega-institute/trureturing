using System.Reflection;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class RelationCorpusTests(ITestOutputHelper output)
{
    private const int MaximumUnreadableDefinitions = 5583;

    [Fact]
    public void EveryStaticRelationProjectionMatchesExecution()
    {
        var root = FindRoot();
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).Order(StringComparer.Ordinal).ToArray();
        var verifier = typeof(ScribeCli).Assembly.GetType("StrataLint.Scribe.RelationVerifier");
        Assert.NotNull(verifier);
        var result = verifier.GetMethod("Verify")!.Invoke(null, [root, paths])!;
        var text = new StringWriter();
        var error = new StringWriter();
        var exit = (int)result.GetType().GetMethod("Write")!.Invoke(result, [text, error])!;
        output.WriteLine(text.ToString());
        output.WriteLine(error.ToString());
        Assert.Equal(0, result.GetType().GetProperty("HostFailures")!.GetValue(result));
        Assert.Equal(0, result.GetType().GetProperty("Mismatches")!.GetValue(result));
        var unreadable = (int)result.GetType().GetProperty("Unreadable")!.GetValue(result)!;
        Assert.InRange(unreadable, 0, MaximumUnreadableDefinitions);
        Assert.Equal(unreadable == 0 ? 0 : 1, exit);
    }

    private static string FindRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
            if (File.Exists(Path.Combine(directory.FullName, "global.json"))
                && Directory.Exists(Path.Combine(directory.FullName, "Blueprint"))) return directory.FullName;
        throw new DirectoryNotFoundException("repository root was not found");
    }
}
