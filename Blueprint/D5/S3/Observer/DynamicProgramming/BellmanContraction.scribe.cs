using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.DynamicProgramming;

internal sealed class BellmanContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The discounted Bellman operator is a strict contraction with prediction distance "
            + "as its unique fixed point.",
        H("Bellman Contraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bellman-operator-contracts-to-prediction-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/DynamicProgramming/BellmanContraction."
                    + "bellman_operator_contracting_unique_fixed_point"),
                H("The Bellman operator contracts to the prediction distance"),
                StatementSource.FromAuthor(ContractionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite nonempty state space. Fix an update, a readout, "
                        + "and a nonnegative real discrepancy bounded by D. For a discount "
                        + "factor gamma strictly between zero and one, the Bellman operator "
                        + "takes the maximum of the current discrepancy and the discounted "
                        + "continuation value.")),
                    Paragraph(Text(
                        "The max operation is nonexpansive, while the continuation term "
                        + "multiplies uniform distance by gamma. Hence the operator is a "
                        + "strict contraction. The previously established Bellman equation "
                        + "makes discounted prediction distance a fixed point, and contraction "
                        + "uniqueness identifies it as the only fixed point.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied "
                        + "ContractingWith.fixedPoint_unique' and "
                        + "abs_max_sub_max_le_abs, both applied by the module. Repository "
                        + "search found the Bellman equation but no contraction or unique "
                        + "fixed-point theorem for this operator. LeanSearch returned HTTP 404."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Bellman(Formula value) =>
        Apply(Seq(F.Id("T"), Underscore, Grp(GammaLower)), value);

    private static Formula ContractionFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula p = F.Id("p");
        Formula d = Seq(F.Id("d"), Underscore, Grp(F.Id("O")));
        Formula predictionDistance = Seq(F.Id("d"), Underscore, Grp(GammaLower));
        Formula distanceBound = Seq(
            Forall, Sp, a, Comma, Sp, b, InMacro, Sp, F.Id("O"), Comma, Sp,
            D(0), Leq, Sp, Seq(d, Open, a, Comma, Sp, b, Close),
            Leq, Sp, F.Id("D"));

        return Disp(Seq(
            Forall, Sp, F.Id("Y"), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
            CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
            CloseBracket, Comma, Sp,
            Forall, Sp, GammaLower, InMacro, Open, D(0), Comma, Sp, D(1), Close,
            Comma, Sp, distanceBound, Sp, Rightarrow, Sp,
            Operatorname, Grp(F.Id("Contracting")), Open,
            Seq(F.Id("T"), Underscore, Grp(GammaLower)), Comma, Sp, GammaLower,
            Close, Sp, Land, Sp,
            Forall, Sp, p, Comma, Sp,
            Open, Bellman(p), Eq, p, Sp, Leftrightarrow, Sp,
            p, Eq, predictionDistance, Close, Dot));
    }
}
