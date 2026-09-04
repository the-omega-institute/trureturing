using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class CompletedScalarOddCouplingDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/CompletionDynamics/ObserverJet/CompletedScalarOddCoupling."
            + "completed_scalar_has_no_linear_odd_coupling";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflection-invariant analytic scalar has no linear or odd homogeneous response.",
        H("Completed Scalar Odd Coupling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completed-scalar-has-no-linear-odd-coupling"),
                DeclarationHandle.Create(Declaration),
                H("A completed scalar has no linear odd coupling"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a scalar readout on a real normed space admit a formal power "
                            + "series at zero and be invariant under reflection of its input.")),
                    Paragraph(Text(
                        "Restricting the readout to every real line gives two equal one-variable "
                            + "power series, one in each orientation. Uniqueness then forces every "
                            + "odd diagonal coefficient to vanish.")),
                    Paragraph(Text(
                        "The linear coefficient is the Frechet derivative. Consequently the "
                            + "derivative is zero, and every positive degree with a nonzero "
                            + "homogeneous diagonal term is even and at least two."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula space = F.Id("E");
        Formula completedScalar = F.Id("completedScalar");
        Formula series = F.Id("series");
        Formula degree = F.Id("n");
        Formula input = F.Id("u");
        Formula index = F.Id("i");
        Formula diagonal = Grp(
            LambdaLower, Sp, index, Colon, Sp, Call("Fin", degree), Sp,
            Mapsto, Sp, input);
        Formula coefficient = At(new Formula.Subscript(series, degree), diagonal);
        Formula exchange = Seq(
            Forall, Sp, input, Colon, Sp, space, Comma, Sp,
            At(completedScalar, input), Sp, Eq, Sp,
            At(completedScalar, Seq(Minus, input)));
        Formula oddTerms = Seq(
            Forall, Sp, degree, Colon, Sp, natural, Comma, Sp,
            Call("Odd", degree), Sp, Rightarrow, Sp,
            Forall, Sp, input, Colon, Sp, space, Comma, Sp,
            coefficient, Sp, Eq, Sp, D(0));
        Formula firstNonconstant = Seq(
            Forall, Sp, degree, Colon, Sp, natural, Comma, Sp,
            D(0), Sp, Lt, Sp, degree, Sp, Land, Sp,
            Open, Exists, Sp, input, Colon, Sp, space, Comma, Sp,
            coefficient, Sp, Neq, Sp, D(0), Close, Sp, Rightarrow, Sp,
            Call("Even", degree), Sp, Land, Sp, D(2), Sp, Leq, Sp, degree);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, space, Colon, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            Call("NormedAddCommGroup", space), Sp, Land, Sp,
            Call("NormedSpace", real, space), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, completedScalar, Colon, Sp,
            new Formula.TypeArrow(space, real), Comma, Sp,
            series, Colon, Sp, Call("FormalMultilinearSeries", real, space, real),
            Comma, RowBreak, Grp(),
            Call("HasFPowerSeriesAt", completedScalar, series, D(0)), Sp, Land, Sp,
            Open, exchange, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("fderiv", real, completedScalar, D(0)), Sp, Eq, Sp, D(0),
            Sp, Land, RowBreak, Grp(),
            Open, oddTerms, Close, Sp, Land, RowBreak, Grp(),
            Open, firstNonconstant, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
