using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class TwelveOrbitMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twelvefold symmetry counts equal orbits by their stabilizer.",
        H("Twelvefold Orbit Multiplicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("twelvefold-equal-orbits-have-stabilizer-weighted-count"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/TwelveOrbitMultiplicity."
                    + "twelve_orbit_multiplicity"),
                H("Twelvefold orbit multiplicity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("G"), Comma, Sp, F.Id("X"), Comma, Sp,
                    F.Id("Y"), Comma, Sp, F.Id("x"), Comma, Sp, F.Id("O"), Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("G"), Close,
                    Sp, Eq, Sp, D(1, 2), Comma, Sp,
                    F.Id("Y"), Sp, Equiv, Sp,
                    Operatorname, Grp(F.Id("Fin")), Open, F.Id("O"), Close,
                    Sp, Times, Sp,
                    Operatorname, Grp(F.Id("orbit")), Open,
                    F.Id("G"), Comma, Sp, F.Id("x"), Close, Comma, Esc,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("Y"), Close,
                    Sp, Times, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("stabilizer")), Open,
                    F.Id("G"), Comma, Sp, F.Id("x"), Close, Close,
                    Sp, Eq, Sp, D(1, 2), Sp, Times, Sp, F.Id("O"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("Y"), Close,
                    Sp, Eq, Sp, D(1, 2), Sp, Times, Sp, F.Id("O"), Slash,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("stabilizer")), Open,
                    F.Id("G"), Comma, Sp, F.Id("x"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If Y is the disjoint parameterization of O copies of one orbit under "
                        + "a finite group G of cardinality twelve, Mathlib's exact "
                        + "orbit-stabilizer identity gives card(Y) times the stabilizer size "
                        + "equals 12O. Nonemptiness of the stabilizer then gives exact natural-"
                        + "number division and the recorded multiplicity formula.")),
                    Paragraph(Text(
                        "This closes only the multiplicity formula in appendix E.78. The four "
                        + "numerical examples, oriented narrow-class account, and glide "
                        + "interpretation in the same atom are not asserted."))),
                DescribeRole.Theorem))));
}
