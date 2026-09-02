using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RhImpliesWeilPositivityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaBridge/RhImpliesWeilPositivity."
            + "riemannHypothesis_implies_o6WeilPositivityStatement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Riemann hypothesis implies the transcribed O-6 Weil positivity statement for "
            + "every supplied zero data set and Weil test function.",
        H("RH Implies the Transcribed O-6 Weil Positivity Statement"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-implies-transcribed-o6-weil-positivity"),
            DeclarationHandle.Create(Declaration),
            H("RH implies the transcribed O-6 Weil positivity statement"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This is the verbatim unfolding of Hearts "
                        + "o6WeilPositivityStatement. Hearts is an OPEN X_Frontier source, not "
                        + "a frozen declaration, and a freezable module cannot import "
                        + "X_Frontier. The proposition body is therefore transcribed while the "
                        + "atom's theorem name is preserved verbatim.")),
                Paragraph(Text(
                    "Under RH, the frozen R-E bridge puts every supplied ZeroData zero on the "
                        + "critical line. The frozen finite convolution-square theorem makes "
                        + "every truncated real sum nonnegative, and truncatedZeroSum_tendsto "
                        + "plus closedness of the nonnegative ray passes that inequality to "
                        + "zeroSum.")),
                Paragraph(Text(
                    "The route volume names truncatedCriticalConvolutionSquareSum_re_nonnegative, "
                        + "which does not exist; the actual frozen theorem is "
                        + "critical_line_truncated_sum_real_nonnegative. Its proposed "
                        + "critical_offline_split_tendsto_explicit_formula route also requires "
                        + "an extra ArchimedeanConvergent hypothesis, so the proof instead uses "
                        + "the symmetric zero-sum limit and closedness.")),
                Paragraph(Text(
                    "The theorem holds even when ZeroData is empty. It is not advertised as a "
                        + "non-vacuous Weil positivity result."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("g");
        Formula zeroWitness = F.Id("hZero");
        Formula convolutionSquare = Call("convolutionSquare", test);
        Formula zeroSide = Call("zeroSum", zeros, convolutionSquare, zeroWitness);
        Formula hypothesis = Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));
        Formula conclusion = Seq(
            Forall, Sp, zeros, Colon, Sp,
            Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            Forall, Sp, test, Colon, Sp,
            Operatorname, Grp(F.Id("WeilTestFunction")), Comma, Sp,
            Forall, Sp, zeroWitness, Colon, Sp,
            Call("SymmetricConvergent", zeros, convolutionSquare), Comma, Sp,
            D(0), Sp, Leq, Sp, Re, Open, zeroSide, Close);

        return Disp(Implies(hypothesis, conclusion));
    }
}
