using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenSeparationBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/GoldenSeparationBound.golden_separation_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct integer points in a finite golden-slope window have an explicit "
            + "positive minimum spectral spacing.",
        H("Golden Separation Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-separation-bound"),
            DeclarationHandle.Create(Declaration),
            H("Finite golden-slope windows are uniformly separated"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here H is a natural number at least two, R_H is the integer square "
                        + "{1,...,H}^2, and E_phi(m,n)=m phi+n. The Lean definition of "
                        + "delta_phi(H) is the minimum of |E_phi(x)-E_phi(y)| over all "
                        + "distinct x and y in R_H.")),
                Paragraph(Text(
                    "For the coordinate differences a and b, the repository's actual "
                        + "golden-integer carrier packages b+a phi. Its real embedding, "
                        + "conjugation, and integer norm give an absolute norm at least "
                        + "one. The conjugate embedding is bounded by phi(H-1), which "
                        + "yields the displayed lower bound for every distinct pair and "
                        + "therefore for the finite minimum."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula size = F.Id("H");
        Formula separation = Seq(
            F.Id("delta"), Underscore, Grp(Varphi), Open, size, Close);
        Formula denominator = Grp(
            Varphi, Sp, Open, size, Sp, Minus, Sp, D(1), Close);

        return Disp(Seq(
            Forall, Sp, size, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(2), Sp, Leq, Sp, size, Sp, Rightarrow, Sp,
            Frac, Grp(D(1)), denominator, Sp, Leq, Sp, separation, Dot));
    }
}
