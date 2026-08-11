using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ScaledPoleAccumulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/ScaledPoleAccumulation",
            "Scaled candidate poles converge to any targeted point on the imaginary axis."),
        H("Scaled Candidate-Pole Accumulation"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("scaled-candidate-poles-approach-the-imaginary-axis"),
                H("Scaled candidate poles approach the imaginary axis"),
                LeanTheorem(
                    "D5/S3/Analytic/ScaledPoleAccumulation."
                    + "scaled_candidate_poles_tendsto"),
                Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty),
                    Left, Open,
                    Frac, Grp(D(1)), Grp(D(2), F.Id("c"), Underscore, F.Id("n")),
                    Plus, F.Id("i"),
                    Frac, Grp(Gamma, Underscore, F.Id("n")),
                    Grp(F.Id("c"), Underscore, F.Id("n")),
                    Right, Close, Eq, F.Id("i"), F.Id("t"))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let c_n be real scales tending to positive infinity and let gamma_n "
                        + "be real heights with gamma_n/c_n tending to a target t. The complex "
                        + "points 1/(2c_n) + i gamma_n/c_n then converge to it: the real parts "
                        + "vanish by inversion at infinity, while the imaginary parts converge "
                        + "by the supplied normalized-height limit.")),
                    Paragraph(Text(
                        "The declaration isolates the scaling step in the source atom. It does "
                        + "not prove that zeros of a particular analytic function provide the "
                        + "height approximation; that number-theoretic distribution input is "
                        + "an explicit hypothesis rather than an imported claim.")))
            ))));
}
