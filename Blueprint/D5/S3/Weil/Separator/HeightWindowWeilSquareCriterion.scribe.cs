using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class HeightWindowWeilSquareCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/HeightWindowWeilSquareCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative to supplied zero data, critical-line location in every spectral-radius "
            + "window is characterized by truncated Weil-square positivity, and the "
            + "all-height condition is equivalent to RH.",
        H("Height-Window Weil-Square Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("height-window-rh-iff-truncated-weil-square-positivity"),
                DeclarationHandle.Create(
                    Prefix + "heightWindow_rh_iff_truncatedWeilSquarePositivity"),
                H("Critical-line location in a height window is equivalent to positivity"),
                StatementSource.FromAuthor(HeightWindowCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward implication identifies the critical-line filter with "
                            + "the full finite cutoff and applies the frozen critical-line "
                            + "truncated-sum nonnegativity theorem. The reverse implication "
                            + "uses the frozen finite-cutoff separator: any off-line index "
                            + "would produce a strictly negative truncated Weil square.")),
                    Paragraph(Text(
                        "The height window is the spectral-radius condition "
                            + "norm(Z.gamma n) <= T, not a bound on the imaginary part of a "
                            + "zero. Positivity means this repository's truncatedZeroSum and "
                            + "convolutionSquare positivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-forall-height-window"),
                DeclarationHandle.Create(Prefix + "rh_iff_forall_heightWindow"),
                H("RH is equivalent to critical-line location at every height"),
                StatementSource.FromAuthor(AllHeightCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RH locates every zero represented by the supplied ZeroData on the "
                            + "critical line. Conversely, exhaustiveness places any zero in "
                            + "the spectral-radius window at its own radius, and the frozen "
                            + "right-half-strip reduction then yields RH.")),
                    Paragraph(Text(
                        "Both equivalences are relative to a supplied ZeroData; this document "
                            + "does not assert that ZeroData exists, and the M1-b existence "
                            + "obligation remains open. The result is not an unconditional "
                            + "proof of the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));

    private static Formula HeightWindowCriterionFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula cutoff = F.Id("T");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("T", Reals())],
            Iff(WindowCriticalLine(zeroData, cutoff),
                TruncatedPositivity(zeroData, cutoff))));
    }

    private static Formula AllHeightCriterionFormula()
    {
        Formula zeroData = F.Id("Z");
        Formula cutoff = F.Id("T");

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Iff(
                RiemannHypothesis(),
                ForAll(
                    [Bound("T", Reals())],
                    WindowCriticalLine(zeroData, cutoff)))));
    }

    private static Formula WindowCriticalLine(Formula zeroData, Formula cutoff)
    {
        Formula index = F.Id("n");
        Formula zero = Call("zero", zeroData, index);
        Formula window = Call("symmetricIndices", zeroData, cutoff);

        return ForAll(
            [Bound("n", Naturals())],
            Implies(
                Member(index, window),
                Equal(RealPart(zero), F.Id("criticalAbscissa"))));
    }

    private static Formula TruncatedPositivity(Formula zeroData, Formula cutoff)
    {
        Formula test = F.Id("g");
        Formula square = Call("convolutionSquare", test);
        Formula truncated = Call("truncatedZeroSum", zeroData, square, cutoff);

        return ForAll(
            [Bound("g", F.Id("WeilTestFunction"))],
            LessOrEqual(D(0), RealPart(truncated)));
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
