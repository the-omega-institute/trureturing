using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenCell5040CongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five small multiplicative orders and coprime CRT determine the power residue on the 5040 cell.",
        H("Power Congruence on the 5040 Cell"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cell-5040-congruence"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/GoldenResource/GoldenCell5040Congruence.goldenCell5040_modEq_2241"),
                H("The common residue is 2241"),
                StatementSource.FromAuthor(CongruenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hypothesis is membership in the set containing 5040, 10080, 15120, "
                        + "20160, 30240 and 60480. Write each member as a power of three times m. "
                        + "The exponent of three is two or three, and m is 560, 1120 or 2240.")),
                    Paragraph(Text(
                        "The multiplicative orders of three modulo 16, 32, 64, 5 and 7 are "
                        + "respectively 4, 8, 16, 4 and 6. Each relevant order divides the member n, "
                        + "so the power of three with exponent n is congruent to one modulo each "
                        + "prime-power factor of m. Coprime CRT combines these congruences.")),
                    Paragraph(Text(
                        "Since m divides 2240, the target 2241 has residue one modulo m. "
                        + "Both the target and the power of three are divisible by the "
                        + "three-primary factor of n. A second coprime CRT step gives the claim. "
                        + "The large power is kept symbolic throughout the synthesis.")),
                    Paragraph(Text(
                        "This is a repository-derived statement. The upstream search reported "
                        + "OEIS A066601 as the general sequence of power residues, and did not "
                        + "find this six-member statement in the sources searched. That search "
                        + "was not exhaustive and establishes no claim of literature priority."))),
                DescribeRole.Theorem))));

    private static Formula CongruenceFormula() => Disp(Seq(
        Forall, Sp, F.Id("n"), Sp, InMacro, Sp,
        new Formula.SetLiteral([D(5,0,4,0), D(1,0,0,8,0), D(1,5,1,2,0),
            D(2,0,1,6,0), D(3,0,2,4,0), D(6,0,4,8,0)]), Comma, Sp,
        new Formula.Power(D(3), F.Id("n")), Sp, Equiv, Sp, D(2,2,4,1), Sp,
        Open, Mathrm, Grp(F.Id("mod")), Sp, F.Id("n"), Close));
}
