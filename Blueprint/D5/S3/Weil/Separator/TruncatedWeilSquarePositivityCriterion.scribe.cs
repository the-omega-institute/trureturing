using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class TruncatedWeilSquarePositivityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/TruncatedWeilSquarePositivityCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative to supplied zero data, nonnegativity of every finite symmetric "
            + "truncated repository Weil-square zero sum is equivalent to the Riemann "
            + "hypothesis.",
        H("Truncated Weil-Square Positivity Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truncated-weil-square-positivity-implies-rh"),
                DeclarationHandle.Create(
                    Prefix + "truncatedWeilSquarePositivity_implies_rh"),
                H("Truncated Weil-square positivity implies RH"),
                StatementSource.FromAuthor(ReverseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A zero in the open right half-strip is represented by the supplied "
                        + "ZeroData. At the cutoff equal to its spectral radius, the frozen "
                        + "off-line separator gives a negative truncated Weil-square sum, "
                        + "contradicting universal nonnegativity. The frozen right-half-strip "
                        + "reduction then gives RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-implies-truncated-weil-square-positivity"),
                DeclarationHandle.Create(
                    Prefix + "rh_implies_truncatedWeilSquarePositivity"),
                H("RH implies truncated Weil-square positivity"),
                StatementSource.FromAuthor(ForwardFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under RH, the frozen critical-line bridge turns the critical-line "
                        + "filter of every symmetric cutoff into the whole cutoff. The frozen "
                        + "finite convolution-square theorem then supplies nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-truncated-weil-square-positivity"),
                DeclarationHandle.Create(
                    Prefix + "rh_iff_truncatedWeilSquarePositivity"),
                H("RH is equivalent to truncated Weil-square positivity"),
                StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equivalence is relative to a supplied ZeroData. It does not "
                            + "assert that ZeroData exists; the M1-b existence obligation "
                            + "remains open.")),
                    Paragraph(Text(
                        "truncatedZeroSum is a sum over symmetricIndices T, exactly the "
                            + "zeros with spectralRadius at most T. This is a finite set, so "
                            + "the statement has no convergence obligation.")),
                    Paragraph(Text(
                        "This is the repository's positivity criterion, not Weil's literal "
                            + "criterion. Since it is conditional on supplied zero data, the "
                            + "equivalence is not an unconditional proof of RH."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ReverseFormula()
    {
        Formula zeroData = F.Id("Z");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Implies(Positivity(zeroData), RiemannHypothesis())));
    }

    private static Formula ForwardFormula()
    {
        Formula zeroData = F.Id("Z");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Implies(RiemannHypothesis(), Positivity(zeroData))));
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
        Formula cutoff = F.Id("T");
        Formula test = F.Id("g");
        Formula square = Call("convolutionSquare", test);
        Formula zeroSide = Call("truncatedZeroSum", zeroData, square, cutoff);

        return ForAll(
            [Bound("T", Reals()), Bound("g", F.Id("WeilTestFunction"))],
            LessOrEqual(D(0), RealPart(zeroSide)));
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

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
