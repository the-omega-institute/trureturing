using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class GoldenCubicBlockNonFifthPowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual Lucas cubic block is not a fifth power by an induction over every positive depth.",
        H("Golden Cubic Blocks Are Not Fifth Powers"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-block-not-fifth-power"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/GoldenCubicBlockNonFifthPower.golden_cubic_block_not_fifth_power"),
            H("No golden cubic block is an integer fifth power"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                D(1), Sp, Le, Sp, F.Id("j"), Sp, Rightarrow, Sp,
                new Formula.Not(Seq(
                    Exists, Sp, F.Id("t"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    new Formula.Power(F.Id("t"), D(5)), Sp, Eq, Sp,
                    Add(new Formula.Power(
                        new Formula.Subscript(F.Id("L"), new Formula.Power(D(3), F.Id("j"))),
                        D(2)), D(3))))))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/bugeaud2006lebesguenagell")),
            Blocks(Paragraph(Text(
                "The integer exclusion is a specialization of the classical D=3 "
                + "Lebesgue-Nagell result recorded in the cited literature: x^2+3 is not "
                + "an integer fifth power. Substitute x=L_(3^j). The repository formal "
                + "proof uses the following modular argument, with no novelty claim. "
                + "The convention is L_n = trace(phi^n), with L_1 = 1. The existing actual "
                + "Lucas recurrence sends x to x(x^2+3) at power-of-three indices. Induction "
                + "over all j >= 1 gives the orbit 4, 10, 7, 1 modulo 11. The block has "
                + "residue 8 or 4, whereas fifth powers have residue 0, 1, or 10. "
                + "The finite checks establish the transition and obstruction; the theorem "
                + "ranges over every positive depth and every integer, including even depths. "
                + "This supplies the exponent-five part of DCE.1-DCE.2 and excludes "
                + "the single-prime fifth-power alternative in DCE.3. It does not supply "
                + "their arbitrary-exponent exclusion or close those parent obligations. "
                + "For the original natural block B_j = natAbs(L_(3^j)^2+3), nonnegativity "
                + "identifies its integer cast with this radicand. If a rational q satisfies "
                + "q^5 = B_j, it is integral over the integers, since its fifth power is an "
                + "integer. Integral closedness gives an integer q, contradicting the theorem. "
                + "The prime-exponent Kummer polynomial criterion at exponent 5 then gives "
                + "irreducibility of X^5-C(B_j) over the rationals. These are applications "
                + "of this theorem and the existing integrality and irreducibility APIs. "
                + "They do not establish a compositum degree, an earlier-prime splitting "
                + "condition, a Frobenius class, a density statement or a Wall-Sun-Sun conclusion."))),
            DescribeRole.Theorem))));
}
