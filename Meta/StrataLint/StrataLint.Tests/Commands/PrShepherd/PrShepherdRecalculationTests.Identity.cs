namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void OpenUsesGhAppTokenOnlyForPullRequestCreation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunOpen(ghAppAvailable: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                "gh:pr create --repo the-omega-institute/trureturing --base dev --head feature --title fixture title --fill-first"
                    + $"|GH_TOKEN={ShepherdFixture.GhAppToken}",
                "gh:pr merge 42 --repo the-omega-institute/trureturing --auto --merge|GH_TOKEN=<unset>",
            ],
            fixture.MutationCalls());
    }

    [Fact]
    public void OpenWithoutGhAppRetainsLocalIdentityForCreationAndAutoMerge()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture();

        var result = fixture.RunOpen(ghAppAvailable: false);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                "gh:pr create --repo the-omega-institute/trureturing --base dev --head feature --title fixture title --fill-first|GH_TOKEN=<unset>",
                "gh:pr merge 42 --repo the-omega-institute/trureturing --auto --merge|GH_TOKEN=<unset>",
            ],
            fixture.MutationCalls());
    }
}
