using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed partial class OpenProblemResolutionClaimTests
{
    [Theory]
    [InlineData("theorem", true, true)]
    [InlineData("def", true, false)]
    [InlineData("theorem", false, false)]
    public void ScopedResolutionChecksForeignLeanMembersWithoutLoadingForeignScribe(
        string kind, bool frozen, bool accepted)
    {
        WithRepository(root =>
        {
            AddOtherFrozenModule(root);
            if (!frozen) File.Delete(Path.Combine(root, "Golden/Frozen/state/" + OtherModuleGid + ".lean.json"));
            Write(root, "Blueprint/" + OtherModuleGid + ".scribe.cs", "invalid C#", Encoding.UTF8);
            var claim = new OpenProblemResolutionClaim(ProblemSlugRef.Create(ProblemSlug),
                ResolutionKind.Proved, [DeclarationHandle.Create(OtherTheoremGid)]);
            var document = CreateDocument(ClaimDescribe(claim: claim));
            var findings = DescribeRepositoryValidator.Validate(root, [document],
                Report((TheoremGid, "theorem"), (OtherTheoremGid, kind)), singleDocument: true);
            if (accepted) Assert.Empty(findings);
            else Assert.Contains(findings, static finding => finding.Code == "invalid-problem-resolution-source");
        });
    }

    [Fact]
    public void ScopedResolutionStillRequiresEachLocalMemberToHaveOneDescribe()
    {
        WithRepository(root =>
        {
            const string local = ModuleGid + ".another_theorem";
            var claim = new OpenProblemResolutionClaim(ProblemSlugRef.Create(ProblemSlug),
                ResolutionKind.Proved, [DeclarationHandle.Create(local)]);
            var findings = DescribeRepositoryValidator.Validate(root,
                [CreateDocument(ClaimDescribe(claim: claim))],
                Report((TheoremGid, "theorem"), (local, "theorem")), singleDocument: true);
            Assert.Contains(findings, static finding => finding.Code == "invalid-problem-resolution-source"
                && finding.Message.Contains("found 0", StringComparison.Ordinal));
        });
    }
}
