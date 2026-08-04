using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class GeometricWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/GeometricWeights",
            "No nonzero rational rescaling of geometric weights matches every singleton W weight."),
        H("Geometric Weights No-Go"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("geometric-weights-do-not-match-singleton-w-weights"),
                H("Geometric weights do not match singleton W weights"),
                LeanTheorem(
                    "D5/S0/Conventions/GeometricWeights."
                    + "no_geometric_weights_match_zeckendorf_singletons"),
                GeometricNoGoFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The W-digit convention defines wValue k as fib(k+2), so singleton bits have "
                    + "weights 1, 2, 3 at indices 0, 1, 2. The first two equations force the "
                    + "geometric ratio to be 2, while the third requires its square to be 3; "
                    + "the nonzero scale excludes cancellation.")))))));

    private static Formula GeometricNoGoFormula()
    {
        Formula equation = Equal(
            Multiply(DefinitionDsl.Id("w1"), new Formula.Power(DefinitionDsl.Id("Lambda"), DefinitionDsl.Id("k"))),
            Multiply(DefinitionDsl.Id("c"), new Formula.Subscript(DefinitionDsl.Id("F"), Add(DefinitionDsl.Id("k"), Num(2)))));
        Formula allIndices = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            DefinitionDsl.Id("Naturals"),
            equation);
        return In(Seq(Neg, Exists, Thin, F.Id("w"), Underscore, D(1), Comma, Lambda, Comma, F.Id("c"), InMacro, Mathbb, Grp(F.Id("Q")), Comma, Esc, F.Id("c"), Neq, D(0), Colon, Esc, F.Id("w"), Underscore, D(1), Lambda, Caret, F.Id("k"), Eq, F.Id("cF"), Underscore, Grp(F.Id("k"), Plus, D(2)), Esc, F.Text, Grp(F.Id("for"), Sp, F.Id("every"), Sp), F.Id("k"), Ge, D(0), Dot));
    }
}
