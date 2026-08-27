using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;
using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

namespace StrataLint.Scribe.Tests;

public sealed class ConceptDynamicsFormalAnswerDocumentTests
{
    [Fact]
    public void SelfFormationFreeWillBoundaryConstructsThreeDeclarations()
    {
        var document = new SelfFormationFreeWillBoundaryDocument().Create().Document;
        var describes = document.Content.Items.OfType<DocumentBlock.Describe>().ToArray();

        Assert.Equal(
            "D5/S3/ConceptDynamics/Agency/SelfFormationFreeWillBoundary",
            document.Header.Gid.Value);
        Assert.Equal(3, describes.Length);
        Assert.Contains(
            @"\operatorname{Nonempty}\left(future\left(h\right)\right)",
            LatexWriter.WriteStatement(describes[0].StatementFormula!),
            StringComparison.Ordinal);
    }

    [Fact]
    public void UniversalValueRoleInvarianceConstructsThreeDeclarations()
    {
        var document = new UniversalValueRoleInvarianceDocument().Create().Document;
        var describes = document.Content.Items.OfType<DocumentBlock.Describe>().ToArray();

        Assert.Equal(
            "D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance",
            document.Header.Gid.Value);
        Assert.Equal(3, describes.Length);
        var counterexample = LatexWriter.WriteStatement(describes[2].StatementFormula!);
        Assert.Contains(@"\neg", counterexample, StringComparison.Ordinal);
        Assert.Contains(
            @"\operatorname{NamedPrivilege}",
            counterexample,
            StringComparison.Ordinal);
    }
}
