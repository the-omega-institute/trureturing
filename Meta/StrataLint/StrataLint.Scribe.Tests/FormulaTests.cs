using System.Collections.Immutable;

namespace StrataLint.Scribe.Tests;

public sealed class FormulaTests
{
    [Fact]
    public void IdentifierRejectsSyntaxThatHasDedicatedAstNodes()
    {
        Assert.Throws<ArgumentException>(() => FormulaIdentifier.Create("phi_1"));
    }

    [Fact]
    public void LatexWriterEmitsEmbeddingAndLogGrammarCanonically()
    {
        Formula goldenIdentity = new Formula.Relation(
            new Formula.Power(new Formula.Phi(), Num(2)),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                new Formula.Phi(),
                FormulaBinaryOperator.Add,
                Num(1)));
        Formula logarithmicScale = new Formula.Floor(
            new Formula.Log(
                new Formula.Phi(),
                new Formula.Absolute(
                    new Formula.FunctionCall(
                        FormulaIdentifier.Create("embedding"),
                        [Id("x")]))));

        Assert.Equal("\\varphi^{2} = \\varphi + 1", LatexWriter.Write(goldenIdentity));
        Assert.Equal(
            "\\left\\lfloor\\log_{\\varphi}\\left(\\left|\\operatorname{embedding}\\left(x\\right)\\right|\\right)\\right\\rfloor",
            LatexWriter.Write(logarithmicScale));
    }

    [Fact]
    public void LatexWriterEmitsSubscriptsFractionsAndPsiCanonically()
    {
        Formula indexedPower = new Formula.Power(
            new Formula.Subscript(Id("x"), Id("n")),
            Num(2));
        Formula half = new Formula.Fraction(Num(1), Num(2));
        Formula conjugateIdentity = new Formula.Relation(
            new Formula.Psi(),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                Num(1),
                FormulaBinaryOperator.Subtract,
                new Formula.Phi()));

        Assert.Equal("x_{n}^{2}", LatexWriter.Write(indexedPower));
        Assert.Equal("\\frac{1}{2}", LatexWriter.Write(half));
        Assert.Equal("\\psi = 1 - \\varphi", LatexWriter.Write(conjugateIdentity));
    }

    [Fact]
    public void LatexWriterEmitsModuloSequenceAndSetNotationCanonically()
    {
        Formula phase = new Formula.Modulo(
            new Formula.Binary(Id("n"), FormulaBinaryOperator.Multiply, new Formula.Phi()),
            Num(1));
        Formula sequence = new Formula.Sequence(phase, Id("n"), new Formula.Integers());
        Formula orbit = new Formula.SetBuilder(phase, Id("n"), new Formula.Integers());
        Formula constants = new Formula.SetLiteral(
            ImmutableArray.Create<Formula>(new Formula.Phi(), new Formula.Psi()));

        Assert.Equal(
            "\\left(n \\varphi \\bmod 1\\right)_{n \\in \\mathbb{Z}}",
            LatexWriter.Write(sequence));
        Assert.Equal(
            "\\left\\{n \\varphi \\bmod 1 \\mid n \\in \\mathbb{Z}\\right\\}",
            LatexWriter.Write(orbit));
        Assert.Equal("\\left\\{\\varphi, \\psi\\right\\}", LatexWriter.Write(constants));
    }

    [Fact]
    public void LatexWriterEmitsIdenticalUtf8BytesOnEveryRun()
    {
        Formula formula = new Formula.Fraction(
            new Formula.Binary(Id("a"), FormulaBinaryOperator.Add, Id("b")),
            Id("c"));

        var first = LatexWriter.WriteUtf8(formula);
        var second = LatexWriter.WriteUtf8(formula);

        Assert.Equal(first.ToArray(), second.ToArray());
        Assert.Equal("\\frac{a + b}{c}", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsTheOptionMapSectionPlaceholderCanonically()
    {
        Formula formula = new Formula.FunctionCall(
            FormulaIdentifier.Create("map"),
            [
                new Formula.Binary(
                    Id("n"),
                    FormulaBinaryOperator.Add,
                    new Formula.Placeholder()),
                new Formula.FunctionCall(
                    FormulaIdentifier.Create("logScale"),
                    [Id("x")]),
            ]);

        Assert.Equal(
            "\\operatorname{map}\\left(n + \\mathord{\\cdot}, \\operatorname{logScale}\\left(x\\right)\\right)",
            LatexWriter.Write(formula));
    }

    private static Formula Id(string value) =>
        new Formula.Symbol(FormulaIdentifier.Create(value));

    private static Formula Num(long value) => new Formula.Number(value);
}
