using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class SecondMagnusKernelNormSquareDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/SecondMagnusKernelNormSquare.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify the exact squared strength of the alternating Fourier slot kernel.",
        H("Exact Second-Magnus Kernel Strength"),
        Blocks(Describe.Lean(
            DescribeId.Create("second-magnus-swap-kernel-norm-square"),
            DeclarationHandle.Create(Prefix + "second_magnus_swap_kernel_norm_sq"),
            H("Exact alternating-kernel strength"),
            StatementSource.FromAuthor(NormSquareFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The squared norm of the alternating two-slot Fourier kernel is exactly "
                        + "four times the squared sine of the half time-frequency area.")),
                Paragraph(Text(
                    "Consequently every nonzero frequency gap has an explicit half-turn "
                        + "sample with squared response four. The result is pairwise and "
                        + "asserts no common sampling clock or zeta-zero comparison."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature")),
        ]));

    private static Formula Call(FormulaIdentifier name, params Formula[] arguments) =>
        new Formula.FunctionCall(name, [.. arguments]);

    private static Formula.BoundVariable Bound(FormulaIdentifier name, Formula domain) =>
        new(name, domain);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(value), D(2));

    private static Formula NormSquareFormula()
    {
        Formula frequencyP = F.Id("fp");
        Formula frequencyQ = F.Id("fq");
        Formula time1 = F.Id("t1");
        Formula time2 = F.Id("t2");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        FormulaIdentifier kernel = FormulaIdentifier.Create("K");
        FormulaIdentifier sine = FormulaIdentifier.Create("sin");
        Formula timeGap = Seq(Open, time1, Sp, Minus, Sp, time2, Close);
        Formula frequencyGap = Seq(Open, frequencyP, Sp, Minus, Sp, frequencyQ, Close);
        Formula halfArea = Seq(
            timeGap, Sp, Times, Sp,
            Frac, Grp(frequencyGap), Grp(D(2)));
        Formula left = Square(new Formula.Norm(
            Call(kernel, frequencyP, frequencyQ, time1, time2)));
        Formula right = Seq(
            D(4), Sp, Times, Sp,
            Square(Call(sine, halfArea)));
        Formula conclusion = new Formula.Relation(
            left, FormulaRelationOperator.Equal, right);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound(FormulaIdentifier.Create("fp"), real),
                Bound(FormulaIdentifier.Create("fq"), real),
                Bound(FormulaIdentifier.Create("t1"), real),
                Bound(FormulaIdentifier.Create("t2"), real),
            ],
            conclusion));
    }
}
