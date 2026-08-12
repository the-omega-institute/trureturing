using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class WignerYanaseSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five members of the Wigner-Yanase contraction spectrum are strictly increasing.",
        H("Wigner-Yanase Spectrum Ordering"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wy-contraction-spectrum-strict-order"),
                DeclarationHandle.Create("D5/S3/Constants/WignerYanaseSpectrum.wy_contraction_spectrum_strict_order"),
                H("The five-member Wigner-Yanase spectrum is strictly ordered"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Num(1), Sp, Lt, Sp,
                                    Frac, Grp(Num(1)), Grp(Num(2), Open, Num(1), Minus, Log, Sp, Num(2), Close), Sp, Lt, Sp,
                                    Num(2), Sp, Lt, Sp,
                                    Frac, Grp(Num(6)), Grp(Num(11), Minus, Num(12), Log, Sp, Num(2)), Sp, Lt, Sp,
                                    Frac, Grp(Num(1)), Grp(Num(1), Minus, Log, Sp, Num(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The Wigner-Yanase contraction spectrum reported for the divergence tower consists of "
                                        + "the five values 1, 1/(2(1 - ln 2)), 2, 6/(11 - 12 ln 2), and 1/(1 - ln 2), where "
                                        + "ln 2 denotes the natural logarithm of two. Using the elementary bounds "
                                        + "0.6931471803 < ln 2 < 0.6931471808 (so that 1 - ln 2 > 0 and 11 - 12 ln 2 > 0), each "
                                        + "successive strict inequality reduces to a linear bound on ln 2 and is discharged by "
                                        + "clearing the positive denominators.")),
                                    Paragraph(Text(
                                        "The theorem establishes only this strict ordering of the reported spectrum values; it "
                                        + "does not derive why these are the Wigner-Yanase contraction coefficients, nor does it "
                                        + "cover the J-relations or the partner-anonymity clause of the note."))),
                DescribeRole.Theorem
            ))));
}
