namespace StrataLint.Scribe.Tests;

public sealed class CHSHSpectrumDocumentTests
{
    [Fact]
    public void CHSHSpectrumStatesBothAlgebraicResultsAndExcludesTheProbabilityLaw()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/QuantumBounds/CHSHSpectrum");
        var describes = definition.Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.Equal(
            "D5/S3/QuantumBounds/CHSHSpectrum.chsh_cubic_coefficient",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[0].Statement).Value.Value);
        Assert.Equal(
            "D5/S3/QuantumBounds/CHSHSpectrum.chsh_spectrum",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[1].Statement).Value.Value);
        Assert.All(describes, static describe =>
        {
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });

        var coefficient = LatexWriter.WriteStatement(describes[0].StatementFormula!);
        Assert.Contains(@"\frac{2}{16N^{2}a^{2}}", coefficient, StringComparison.Ordinal);
        Assert.Contains(@"\frac{2}{16N^{2}b^{2}}", coefficient, StringComparison.Ordinal);
        Assert.Contains(
            @"\frac{1}{N^{2}(16-N^{2})}",
            coefficient,
            StringComparison.Ordinal);

        var spectral = LatexWriter.WriteStatement(describes[1].StatementFormula!);
        Assert.Contains(@"\operatorname{spectrum}", spectral, StringComparison.Ordinal);
        Assert.Contains(
            @"\{\sqrt{4+N},-\sqrt{4+N},\sqrt{4-N},-\sqrt{4-N}\}",
            spectral,
            StringComparison.Ordinal);

        var formulas = coefficient + spectral;
        Assert.DoesNotContain(@"\varepsilon", formulas, StringComparison.Ordinal);
        Assert.DoesNotContain("Dirichlet", formulas, StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Pr}", formulas, StringComparison.Ordinal);
        Assert.All(
            describes.SelectMany(static describe => describe.Content.Items)
                .OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
