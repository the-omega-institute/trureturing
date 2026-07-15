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

        Assert.Equal("\\left(x_{n}\\right)^{2}", LatexWriter.Write(indexedPower));
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
            "\\left(n \\cdot \\varphi \\bmod 1\\right)_{n \\in \\mathbb{Z}}",
            LatexWriter.Write(sequence));
        Assert.Equal(
            "\\left\\{n \\cdot \\varphi \\bmod 1 \\mid n \\in \\mathbb{Z}\\right\\}",
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

    [Fact]
    public void RelationChainEmitsConstructivelyWithoutParsingLatex()
    {
        Formula formula = new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [
                new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [Num(89)]),
                new Formula.FunctionCall(FormulaIdentifier.Create("Z"), [Num(123)]),
                new Formula.Subscript(Num(1010000000), Id("W")),
            ]);

        Assert.Equal(
            "\\operatorname{Z}\\left(89\\right) = \\operatorname{Z}\\left(123\\right) = 1010000000_{W}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterParenthesizesRepeatedScriptBases()
    {
        Formula nestedPower = new Formula.Power(
            new Formula.Power(Id("x"), Num(2)),
            Num(3));
        Formula nestedSubscript = new Formula.Subscript(
            new Formula.Subscript(Id("x"), Id("n")),
            Id("m"));

        Assert.Equal("\\left(x^{2}\\right)^{3}", LatexWriter.Write(nestedPower));
        Assert.Equal("\\left(x_{n}\\right)_{m}", LatexWriter.Write(nestedSubscript));
    }

    [Fact]
    public void LatexWriterPreservesMultiplicationByANegatedOperand()
    {
        Formula formula = new Formula.Binary(
            Id("x"),
            FormulaBinaryOperator.Multiply,
            new Formula.Negate(Num(1)));

        Assert.Equal("x \\cdot \\left(-1\\right)", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsANestedRightFactorThatStartsWithNegation()
    {
        Formula formula = new Formula.Binary(
            Id("x"),
            FormulaBinaryOperator.Multiply,
            new Formula.Binary(
                new Formula.Negate(Num(1)),
                FormulaBinaryOperator.Multiply,
                Id("y")));

        Assert.Equal("x \\cdot \\left(-1 \\cdot y\\right)", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsASequenceBeforeApplyingAnotherSubscript()
    {
        Formula formula = new Formula.Subscript(
            new Formula.Sequence(Id("x"), Id("n"), new Formula.Integers()),
            Id("m"));

        Assert.Equal(
            "\\left(\\left(x\\right)_{n \\in \\mathbb{Z}}\\right)_{m}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterEmitsAnExplicitOperatorForNumericMultiplication()
    {
        Formula formula = new Formula.Binary(
            Num(1),
            FormulaBinaryOperator.Multiply,
            Num(2));

        Assert.Equal("1 \\cdot 2", LatexWriter.Write(formula));
    }

    [Fact]
    public void LatexWriterGroupsCrossedScriptChains()
    {
        Formula formula = new Formula.Power(
            new Formula.Subscript(
                new Formula.Power(Id("x"), Num(2)),
                Id("n")),
            Num(3));

        Assert.Equal(
            "\\left(\\left(x^{2}\\right)_{n}\\right)^{3}",
            LatexWriter.Write(formula));
    }

    [Fact]
    public void NegativeNumbersUseTheDedicatedNegateNode()
    {
        Assert.Throws<ArgumentOutOfRangeException>(() => new Formula.Number(-1));
    }

    [Fact]
    public void LatexWriterIsTotalAndDeterministicForTheClosedFormulaVocabulary()
    {
        var identifier = FormulaIdentifier.Create("f");
        var x = Id("x");
        var formulas = new Formula[]
        {
            new Formula.Symbol(identifier),
            Num(1),
            new Formula.Phi(),
            new Formula.Psi(),
            new Formula.Placeholder(),
            new Formula.Integers(),
            new Formula.Negate(x),
            new Formula.Absolute(x),
            new Formula.Binary(x, FormulaBinaryOperator.Add, Num(1)),
            new Formula.Fraction(x, Num(2)),
            new Formula.Subscript(x, Num(1)),
            new Formula.Power(x, Num(2)),
            new Formula.Floor(x),
            new Formula.Log(Num(2), x),
            new Formula.Modulo(x, Num(2)),
            new Formula.Sequence(x, Id("n"), new Formula.Integers()),
            new Formula.SetLiteral([x]),
            new Formula.SetBuilder(x, Id("n"), new Formula.Integers()),
            new Formula.FunctionCall(identifier, [x]),
            new Formula.Relation(x, FormulaRelationOperator.NotEqual, Num(0)),
            new Formula.RelationChain(FormulaRelationOperator.Equal, [x, Num(1)]),
        };

        foreach (var formula in formulas)
        {
            var first = LatexWriter.Write(formula);
            var second = LatexWriter.Write(formula);
            Assert.NotEmpty(first);
            Assert.Equal(first, second);
        }
    }

    [Fact]
    public void FormulaConstructorsRejectMissingChildrenAndDefaultCollections()
    {
        Assert.Throws<ArgumentNullException>(() => new Formula.Negate(null!));
        Assert.Throws<ArgumentNullException>(() => new Formula.Binary(
            null!,
            FormulaBinaryOperator.Add,
            Num(1)));
        Assert.Throws<ArgumentNullException>(() => new Formula.Relation(
            Num(1),
            FormulaRelationOperator.Equal,
            null!));
        Assert.Throws<ArgumentException>(() => new Formula.SetLiteral(default));
        Assert.Throws<ArgumentException>(() => new Formula.FunctionCall(
            FormulaIdentifier.Create("f"),
            default));
        Assert.Throws<ArgumentException>(() => new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [Num(1)]));
    }

    private static Formula Id(string value) =>
        new Formula.Symbol(FormulaIdentifier.Create(value));

    private static Formula Num(long value) => new Formula.Number(value);
}
