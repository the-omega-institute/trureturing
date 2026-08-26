using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;
using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

namespace StrataLint.Scribe.Tests;

public sealed class ConceptDynamicsFormalAnswerDocumentTests
{
    [Fact]
    public void SelfFormationFreeWillBoundaryConstructsThreeDeclarations()
    {
        var document = new SelfFormationFreeWillBoundaryDocument().Create().Document;

        Assert.Equal(
            "D5/S3/ConceptDynamics/Agency/SelfFormationFreeWillBoundary",
            document.Header.Gid.Value);
        Assert.Equal(3, document.Content.Items.OfType<DocumentBlock.Describe>().Count());
    }

    [Fact]
    public void UniversalValueRoleInvarianceConstructsThreeDeclarations()
    {
        var document = new UniversalValueRoleInvarianceDocument().Create().Document;

        Assert.Equal(
            "D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance",
            document.Header.Gid.Value);
        Assert.Equal(3, document.Content.Items.OfType<DocumentBlock.Describe>().Count());
    }
}
