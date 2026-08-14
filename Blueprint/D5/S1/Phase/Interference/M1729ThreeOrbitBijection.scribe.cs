using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class M1729ThreeOrbitBijectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three prime factors of 1729 give exactly three singleton stationing choices.",
        H("1729 Three-Orbit Bijection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("m1729-three-orbit-bijection"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/M1729ThreeOrbitBijection"
                    + ".m1729_three_orbit_bijection"),
                H("The three prime factors give three singleton choices"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(1, 7, 2, 9), Eq, D(7), Cdot, D(1, 3), Cdot, D(1, 9),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Prime")), Open, D(7), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Prime")), Open, D(1, 3), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Prime")), Open, D(1, 9), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("primeFactors")), Open, D(1, 7, 2, 9), Close,
                    Eq, OpenBrace, D(7), Comma, Sp, D(1, 3), Comma, Sp, D(1, 9), CloseBrace,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("Equiv")), Open,
                    OpenBrace, F.Id("S"), Subseteq,
                    Operatorname, Grp(F.Id("primeFactors")), Open, D(1, 7, 2, 9), Close,
                    Mid, Sp, Bar, F.Id("S"), Bar, Eq, D(1), CloseBrace,
                    Comma, Sp, Operatorname, Grp(F.Id("Fin")), Open, D(3), Close,
                    Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first conjunct is the exact factorization. The next three conjuncts "
                        + "certify primality, and the primeFactors equality says that no further "
                        + "prime factor occurs. The final Nonempty Equiv term is a checked bijection "
                        + "from singleton subsets of that exact factor set to Fin 3.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies primeFactors_mul, the singleton prime-factor theorem, "
                        + "and equivFinOfCardEq. The existing three-singleton stationing theorem "
                        + "supplies the final cardinal count, so the declaration does not reprove it.")),
                    Paragraph(Text(
                        "This is a deeper partial closure of the concrete 1729 clause only. The "
                        + "selector, member-table, direction, and prediction clauses in the same "
                        + "source atom are not asserted here."))),
                DescribeRole.Theorem)),
        []));
}
