using Xunit;
using Xunit.Abstractions;

namespace StrataLint.Scribe.Documents.Tests;

public sealed class RelationCorpusTests(ITestOutputHelper output)
{
    private const int MaximumUnreadableDefinitions = 62;

    [Fact]
    public void EveryStaticRelationProjectionMatchesExecution()
    {
        var root = FindRoot();
        var paths = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).Order(StringComparer.Ordinal).ToArray();
        var result = RelationVerifier.Verify(root, paths);
        var text = new StringWriter();
        var error = new StringWriter();
        var exit = result.Write(text, error);
        output.WriteLine($"staticSeconds={result.StaticElapsed.TotalSeconds.ToString(System.Globalization.CultureInfo.InvariantCulture)}");
        foreach (var group in result.Items.Where(item => item.Unreadable is not null).GroupBy(item => item.Unreadable!.Shape).OrderBy(group => group.Key, StringComparer.Ordinal))
            output.WriteLine($"shape={group.Key} definitions={group.Count()}");
        output.WriteLine(text.ToString());
        output.WriteLine(error.ToString());
        Assert.Equal(0, result.HostFailures);
        Assert.Equal(0, result.Mismatches);
        var unreadable = result.Unreadable;
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
