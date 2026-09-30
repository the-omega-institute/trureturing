namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class PreflightLeanDonorTests
{
    [Theory]
    [InlineData("missing-value", false)]
    [InlineData("empty-value", false)]
    [InlineData("duplicate", false)]
    [InlineData("option-as-value", false)]
    [InlineData("missing-value", true)]
    [InlineData("empty-value", true)]
    [InlineData("duplicate", true)]
    [InlineData("option-as-value", true)]
    public void MalformedExplicitDonorIsAnInputError(string scenario, bool writer)
    {
        using var directory = new TemporaryDirectory();
        var options = scenario switch
        {
            "missing-value" => new[] { "--donor-repository" },
            "empty-value" => ["--donor-repository", ""],
            "option-as-value" => ["--donor-repository", "--path"],
            _ => ["--donor-repository", directory.Path, "--donor-repository", directory.Path],
        };
        var result = writer
            ? LeanCacheEnsureCommand.RunWithWriter(directory.Path, [.. options, "--", "unreachable-producer"],
                new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner())
            : LeanCacheEnsureCommand.Run(directory.Path, options,
                new ProductionWorktreeProcessRunner(), new ApfsDirectoryCloner());
        Assert.False(result.Success);
        Assert.StartsWith("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(directory.Path, ".lake")));
    }

}
