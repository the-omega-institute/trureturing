using StrataLint.Engine;
using System.Text;

namespace StrataLint.RepositoryFileMap.Tests;

public sealed class RegPathPolicyTests
{
    [Theory]
    [InlineData("Reg/lakefile.toml")]
    [InlineData("Reg/lake-manifest.json")]
    [InlineData("Reg/D5/S3/Arith/X.lean")]
    [InlineData("Reg/Support/X.lean")]
    [InlineData("Reg/Catalogs/Family/X.lean")]
    public void RegisteredPathsAreAdmittedWithoutMathematicalIdentity(string value)
    {
        var path = RepoPath.CreateKnown(value);
        Assert.Null(RepositoryPathPolicy.Validate(path, Policy()));
        Assert.False(RepositoryPathPolicy.TryResolve(path, out _));
        Assert.False(Gid.TryParse(value[..value.LastIndexOf('.')], out _));
        Assert.False(LeanClosureValidator.IsManagedLean(value));
    }

    [Theory]
    [InlineData("Reg/D9/X.lean")]
    [InlineData("Reg/Foo.lean")]
    [InlineData("Reg/D5/S9/Arith/X.lean")]
    [InlineData("Reg/D5/S0/Arith/X.lean")]
    [InlineData("Reg/D5/S3/Unknown/X.lean")]
    [InlineData("Reg/D5/Foo.lean")]
    [InlineData("Reg/Support/X.json")]
    [InlineData("Reg/lakefile.lean")]
    public void UnregisteredOrInvalidSuffixIsRejected(string value) =>
        Assert.NotNull(RepositoryPathPolicy.Validate(RepoPath.CreateKnown(value), Policy()));

    [Theory]
    [InlineData("Reg/D5/S0/Carrier/Target.lean", true)]
    [InlineData("Reg/D5/S9/Carrier/Target.lean", false)]
    [InlineData("Reg/D5/S3/Carrier/Target.lean", false)]
    [InlineData("Reg/D5/S0/Unknown/Target.lean", false)]
    public void ExactFileMapMembershipStillChecksDeclarationOwner(string value, bool admitted)
    {
        var fileMap = TestFileMap.Canonical.Replace("Reg/D5/**/*.lean", value, StringComparison.Ordinal);
        var policy = PolicyLoadAssert.Accepted(RepositoryPolicyLoader.Load(
            Encoding.UTF8.GetBytes(fileMap), Encoding.UTF8.GetBytes(TestFileMap.Domains))).Policy;

        Assert.Equal(admitted, RepositoryPathPolicy.Validate(RepoPath.CreateKnown(value), policy) is null);
    }

    [Fact]
    public void TraversalIsRejectedBeforePathAdmission() =>
        Assert.False(RepoPath.TryCreate("Reg/D5/../x.lean", out _));

    private static ValidatedPolicy Policy()
    {
        var root = TestRepositoryLayout.FindRoot();
        return PolicyLoadAssert.Accepted(RepositoryPolicyLoader.LoadRepository(root)).Policy;
    }
}
