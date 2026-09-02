using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;
using StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;
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

    [Fact]
    public void AssertionSettlementCeilingConstructsFiveDeclarations()
    {
        var document = new AssertionSettlementCeilingDocument().Create().Document;
        var describes = document.Content.Items.OfType<DocumentBlock.Describe>().ToArray();

        Assert.Equal(
            "D5/S3/ConceptDynamics/Answering/AssertionSettlementCeiling",
            document.Header.Gid.Value);
        Assert.Equal(5, describes.Length);
        var firstMatch = LatexWriter.WriteStatement(describes[0].StatementFormula!);
        Assert.Contains(@"\operatorname{settle}", firstMatch, StringComparison.Ordinal);
        Assert.Contains("notFormalized", firstMatch, StringComparison.Ordinal);
        var soundness = LatexWriter.WriteStatement(describes[4].StatementFormula!);
        Assert.Contains(@"\operatorname{buildSucceeded}", soundness, StringComparison.Ordinal);
    }

    [Fact]
    public void RegisterValidityHistoryConstructsThreeDeclarations()
    {
        var document = new RegisterValidityHistoryDocument().Create().Document;
        var describes = document.Content.Items.OfType<DocumentBlock.Describe>().ToArray();

        Assert.Equal(
            "D5/S3/ConceptDynamics/Answering/RegisterValidityHistory",
            document.Header.Gid.Value);
        Assert.Equal(3, describes.Length);
        var exactlyOne = LatexWriter.WriteStatement(describes[1].StatementFormula!);
        Assert.Contains(@"\operatorname{IsActive}", exactlyOne, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{revise}", exactlyOne, StringComparison.Ordinal);
    }

    [Fact]
    public void RenderCeilingDisclosureConstructsFiveDeclarations()
    {
        var document = new RenderCeilingDisclosureDocument().Create().Document;
        var describes = document.Content.Items.OfType<DocumentBlock.Describe>().ToArray();

        Assert.Equal(
            "D5/S3/ConceptDynamics/Answering/RenderCeilingDisclosure",
            document.Header.Gid.Value);
        Assert.Equal(5, describes.Length);
        var disclosure = LatexWriter.WriteStatement(describes[3].StatementFormula!);
        Assert.Contains("plain", disclosure, StringComparison.Ordinal);
        Assert.Contains("showWork", disclosure, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{render}", disclosure, StringComparison.Ordinal);
    }
}
