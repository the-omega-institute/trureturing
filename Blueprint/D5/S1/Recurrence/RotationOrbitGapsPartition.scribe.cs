using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class RotationOrbitGapsPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Finite rotation orbit gaps partition the unit circle.",
H("Rotation Orbit Gap Partition"),
Blocks(
                Describe.Lean(
                    DescribeId.Create("rotation-orbit-gaps-partition"),
                    DeclarationHandle.Create("D5/S1/Recurrence/RotationOrbitGapsPartition."
                        + "rotation_orbit_gaps_partition"),
                    H("Rotation orbit gaps partition the circle"),
                    StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Alpha, InMacro, Mathbb, Grp(F.Id("R")), Comma, Esc, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Colon, Eq, Operatorname, Grp(F.Id("rotationOrbit")), Open, Alpha, Comma, F.Id("n"), Close, Eq, OpenBrace, Operatorname, Grp(F.Id("fract")), Open, F.Id("k"), Alpha, Close, Mid, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc, F.Id("k"), Lt, F.Id("n"), CloseBrace, Colon, Esc, F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Subseteq, OpenBracket, D(0), Comma, D(1), Close, Esc, Land, Esc, Open, D(0), Lt, F.Id("n"), Rightarrow, Sp, F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Neq, Emptyset, Close, Esc, Land, Esc, Forall, Sp, F.Id("h"), Underscore, F.Id("n"), Colon, D(0), Lt, F.Id("n"), Comma, Esc, Open, Open, Forall, Sp, F.Id("x"), InMacro, Sp, F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Comma, Esc, F.Id("g"), Underscore, Grp(F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Comma, F.Id("h"), Underscore, F.Id("n")), Open, F.Id("x"), Close, Gt, D(0), Close, Esc, Land, Esc, Sum, Underscore, Grp(F.Id("x"), InMacro, Sp, F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n"))), F.Id("g"), Underscore, Grp(F.Id("O"), Underscore, Grp(Alpha, Comma, F.Id("n")), Comma, F.Id("h"), Underscore, F.Id("n")), Open, F.Id("x"), Close, Eq, D(1), Close, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The fractional parts of the first n multiples of a real rotation "
                        + "parameter lie in the half-open unit interval. For positive n, "
                        + "the orbit contains its zeroth point, so the cyclic gap partition "
                        + "applies: every clockwise gap is positive and their sum is one. "
                        + "At parameter one half and length two, the orbit is exactly zero "
                        + "and one half; zero uses the ordinary successor while one half "
                        + "uses the wrap branch."))),
                    DescribeRole.Theorem))));
}
