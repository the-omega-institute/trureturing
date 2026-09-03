using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Isolation;

internal sealed class GoldenAuxiliaryZetaNonzeroDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Isolation/GoldenAuxiliaryZetaNonzero."
            + "riemannZeta_golden_auxiliary_ne_zero";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Riemann zeta is nonzero at the golden auxiliary point one over phi.",
        H("Golden Auxiliary Zeta Nonvanishing"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-auxiliary-zeta-nonzero"),
            DeclarationHandle.Create(Declaration),
            H("Riemann zeta is nonzero at the golden auxiliary point"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This is the next pointwise step in the golden Euler germ extraction "
                        + "ladder of OACTC parts 580 and 581, on the RH-route O-5 control "
                        + "line. It closes the previously open special-value boundary at "
                        + "one over phi by proving that the zeta factor there cannot vanish.")),
                Paragraph(Text(
                    "The proof pairs adjacent terms of the Dirichlet eta series. Each real "
                        + "pair is strictly positive, while a derivative majorant gives "
                        + "absolute convergence for positive real part. An identity-theorem "
                        + "argument transports the usual zeta identity to the positive real "
                        + "axis. The frozen initial O-5 exponent power law identifies the "
                        + "golden coordinate used by the final specialization.")),
                Paragraph(Text(
                    "The exact bracket one half less than one over phi less than one records "
                        + "that the selected value is genuinely inside the critical strip. "
                        + "STOPPING JUSTIFICATION: this is one concrete nonvanishing value. "
                        + "It does not establish O-5, the Riemann hypothesis, any implication "
                        + "toward either claim, or a zero-free region around the point."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula auxiliaryPoint = Fraction(F.D(1), F.Varphi);
        return F.Disp(F.Seq(
            Call("riemannZeta", auxiliaryPoint),
            F.Sp, F.Neq, F.Sp, F.D(0), F.Dot));
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
