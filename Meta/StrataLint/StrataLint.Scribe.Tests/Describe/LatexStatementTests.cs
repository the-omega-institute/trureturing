namespace StrataLint.Scribe.Tests;

using static StrataLint.Scribe.DefinitionDsl;

public sealed class StructuralFormulaContractTests
{
    [Fact]
    public void StructuralNodesRenderWithoutAStringFormulaParser()
    {
        var statement = new Formula.Layout(
            FormulaLayoutMode.Inline,
            Equal(Call("Re", Id("s")), new Formula.Fraction(Num(1), Num(2))));

        Assert.Equal(@"$\operatorname{Re}\left(s\right) = \frac{1}{2}$", LatexWriter.WriteStatement(statement));
    }

    [Fact]
    public void InvalidStructuralCollectionsFailClosed()
    {
        Assert.Throws<ArgumentException>(() => new Formula.Aligned([]));
        Assert.Throws<ArgumentException>(() => new Formula.FunctionCall(
            FormulaIdentifier.Create("f"),
            default));
    }
}
