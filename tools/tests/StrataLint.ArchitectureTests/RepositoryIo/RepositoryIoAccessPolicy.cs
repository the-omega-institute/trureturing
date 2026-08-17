namespace StrataLint.ArchitectureTests;

public sealed class RepositoryIoAccessPolicyTests
{
    [Fact]
    public void RepositoryTestsHaveNoUnapprovedDirectReadsOrAddedExemptions()
    {
        var root = RepositoryLayout.FindRoot();

        Assert.Empty(RepositoryIoAccessPolicy.InspectRepository(root));
        Assert.Empty(RepositoryIoAccessPolicy.FindAddedExemptions(
            RepositoryIoAccessPolicy.DeferredProjectExemptions));
    }
}
