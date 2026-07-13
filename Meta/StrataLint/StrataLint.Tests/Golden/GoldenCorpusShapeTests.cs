namespace StrataLint.Tests;

public sealed class GoldenCorpusShapeTests
{
    [Fact]
    public void CorpusContainsEveryTypedCaseExactlyOnce()
    {
        Assert.Equal(110, GoldenCorpus.All.Count);
        Assert.Equal(
            GoldenCorpus.All.Count,
            GoldenCorpus.All.Select(static item => item.Name).Distinct(StringComparer.Ordinal).Count());
        Assert.All(GoldenCorpus.All, static item => Assert.False(string.IsNullOrWhiteSpace(item.Name)));
    }
}
