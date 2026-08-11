using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class QuarticThirtySixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/Congruence/QuarticThirtySix",
            "The quartic 27k^4+108k^3+171k^2+126k+36 is divisible by 36 for every integer k."),
        H("Quartic Divisibility by Thirty-Six"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("thirty-six-dvd-quartic"),
                H("Thirty-six divides the quartic for every integer"),
                LeanTheorem(
                    "D5/S3/Arith/Congruence/QuarticThirtySix.thirtySix_dvd_m"),
                Disp(Seq(
                    Num(36), Sp, Mid, Sp,
                    Num(27), F.Id("k"), Caret, Grp(D(4)), Plus,
                    Num(108), F.Id("k"), Caret, Grp(D(3)), Plus,
                    Num(171), F.Id("k"), Caret, Grp(D(2)), Plus,
                    Num(126), F.Id("k"), Plus, Num(36))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The quartic m(k) = 27k^4 + 108k^3 + 171k^2 + 126k + 36 is divisible by 36 for every "
                        + "integer k. Reducing modulo 36, the polynomial evaluates to zero on every residue "
                        + "class, so 36 divides m(k) identically. The residue check is a finite kernel decision "
                        + "over the 36 elements of ZMod 36, lifted to the integers by the standard "
                        + "cast-vanishes-iff-divides equivalence.")),
                    Paragraph(Text(
                        "This is the self-contained arithmetic corroboration of the 36-theorem; it makes no claim "
                        + "about the geodesic-word or fixed-point-form context in which the quartic arises.")))))));
}
