namespace StrataLint.Scribe.Tests;

public sealed class RobertsonSchrodingerDocumentTests
{
    [Fact]
    public void RobertsonSchrodingerKeepsTheGramRemainderAndLiteratureProvenance()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/QuantumBounds/RobertsonSchrodinger");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/QuantumBounds/RobertsonSchrodinger.robertson_schrodinger",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.LiteratureAttested(
            describe,
            "D5/L/Quantum/robertson1929uncertainty");
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains("=", latex, StringComparison.Ordinal);
        Assert.Contains("\\operatorname{Cov}", latex, StringComparison.Ordinal);
        Assert.Contains("G", latex, StringComparison.Ordinal);
        Assert.Contains("G \\geq 0", latex, StringComparison.Ordinal);
    }
}
