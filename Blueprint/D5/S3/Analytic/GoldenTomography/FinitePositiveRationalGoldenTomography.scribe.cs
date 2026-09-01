using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class FinitePositiveRationalGoldenTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct positive rational scales have distinct lifted golden "
            + "coordinates and admit exact finite moment and time tomography.",
        H("Finite Positive-Rational Golden Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-positive-rational-golden-time-window-injective"),
                DeclarationHandle.Create("D5/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography.finite_positive_rational_golden_time_window_injective"),
                H("Lifted golden time windows recover finite rational-scale amplitudes"),
                StatementSource.FromAuthor(RationalWindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An injective finite family of positive rational scales remains injective after passage to the existing lifted golden logarithmic coordinate.")),
                    Paragraph(Text(
                        "Vandermonde tomography then reconstructs the hidden amplitudes exactly. The result concerns the universal-cover coordinate and does not assert quotient-circle conditioning."))),
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

    private static Formula RationalWindowFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("q"), Colon, Sp,
        Open, Forall, Sp, F.Id("i"), Comma, Sp,
        D(0), Sp, Lt, Sp,
        new Formula.Subscript(F.Id("q"), F.Id("i")), Close, Sp, Land, Sp,
        Call("Injective", F.Id("q")), Sp, Rightarrow,
        RowBreak, Grp(),
        Call("Injective",
            Call("firstCrystalTimeWindow",
                Seq(F.Id("i"), Sp, Mapsto, Sp,
                    Call("liftedGoldenRationalNode",
                        new Formula.Subscript(F.Id("q"), F.Id("i")))))),
        Dot,
        End, Grp(F.Id("gathered"))));

}
