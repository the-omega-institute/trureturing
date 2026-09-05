using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class WeilSquarePositivityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/WeilSquarePositivityCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative to supplied zero data, nonnegativity of every repository Weil-square "
            + "zero sum implies the Riemann hypothesis and is equivalent to it.",
        H("Weil-Square Positivity Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weil-square-positivity-implies-rh"),
                DeclarationHandle.Create(Prefix + "weilSquarePositivity_implies_rh"),
                H("Weil-square positivity implies the Riemann hypothesis"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A zero in the open right half-strip is a nontrivial zero and is "
                            + "therefore represented by the supplied ZeroData. The frozen "
                            + "off-line separator produces a convolution square with negative "
                            + "zero-sum real part, contradicting the assumed nonnegativity.")),
                    Paragraph(Text(
                        "The frozen right-half-strip reduction turns that exclusion into the "
                            + "Riemann hypothesis. No separator or zeta-reduction fact is "
                            + "reproved here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-weil-square-positivity"),
                DeclarationHandle.Create(Prefix + "rh_iff_weilSquarePositivity"),
                H("RH is equivalent to Weil-square positivity"),
                StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reverse implication is the preceding separator argument. The "
                            + "forward implication is the frozen RH-to-positivity theorem.")),
                    Paragraph(Text(
                        "Both statements are relative to a supplied ZeroData; this module does "
                            + "not assert that ZeroData exists, and the M1-b existence obligation "
                            + "remains open.")),
                    Paragraph(Text(
                        "The right side is positivity for this repository's zeroSum, "
                            + "convolutionSquare, and WeilTestFunction definitions. It is not a "
                            + "literal transcription of Weil's explicit-formula criterion, and "
                            + "the conditional equivalence is not an unconditional proof of RH."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ForwardFormula()
    {
        Formula zeroData = F.Id("Z");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Implies(Positivity(zeroData), RiemannHypothesis())));
    }

    private static Formula EquivalenceFormula()
    {
        Formula zeroData = F.Id("Z");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Iff(RiemannHypothesis(), Positivity(zeroData))));
    }

    private static Formula Positivity(Formula zeroData)
    {
        Formula test = F.Id("g");
        Formula witness = F.Id("hZero");
        Formula square = Call("convolutionSquare", test);
        Formula zeroSide = Call("zeroSum", zeroData, square, witness);

        return ForAll(
            [
                Bound("g", F.Id("WeilTestFunction")),
                Bound("hZero", Call("SymmetricConvergent", zeroData, square)),
            ],
            LessOrEqual(D(0), RealPart(zeroSide)));
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
