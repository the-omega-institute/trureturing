using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenCell902160UniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The order of three modulo 179 selects exactly one member of the scaled cell.",
        H("Uniqueness in the 902160 Cell"),
        Blocks(
            Describe.Lean(DescribeId.Create("exponent-class-modulo-179"),
                DeclarationHandle.Create(Prefix + "three_pow_modEq_179_iff"),
                H("An unbounded exponent characterization"),
                StatementSource.FromAuthor(ExponentFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The order of three modulo 179 is 89: its eighty ninth power is one, "
                    + "three is not one, and 89 is prime. Its twenty third power and 2241 both "
                    + "have residue 93. Equality of powers therefore determines the exponent "
                    + "modulo 89. This statement applies to every natural exponent."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("unique-scaled-cell-member"),
                DeclarationHandle.Create(Prefix + "goldenCell902160_modEq_2241_iff"),
                H("The unique member is 1804320"),
                StatementSource.FromAuthor(CellFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every listed index is divisible by 179. Projecting its power congruence "
                    + "to that modulus forces its exponent to be congruent to 23 modulo 89, "
                    + "which excludes the other five indices. The old prime exponent windows "
                    + "alone do not make these exclusions.")),
                    Paragraph(Text(
                        "For the surviving index, lift the frozen congruence at 10080 to any "
                        + "nonzero multiple of its exponent. The residues modulo 32, 5 and 7 "
                        + "are one, and the residue modulo 9 is zero. Coprime CRT combines "
                        + "these with the congruence modulo 179. The large powers stay symbolic; "
                        + "only small certificates and exponent residues are normalized."))),
                DescribeRole.Theorem))));

    private static Formula ExponentFormula() => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Congruence(new Formula.Power(D(3), N()), D(2,2,4,1), D(1,7,9)), Sp, Iff, Sp,
        Congruence(N(), D(2,3), D(8,9))));

    private static Formula CellFormula() => Disp(Seq(
        Forall, Sp, N(), Sp, InMacro, Sp,
        new Formula.SetLiteral([D(9,0,2,1,6,0), D(1,8,0,4,3,2,0), D(2,7,0,6,4,8,0),
            D(3,6,0,8,6,4,0), D(5,4,1,2,9,6,0), D(1,0,8,2,5,9,2,0)]), Comma, Sp,
        Congruence(new Formula.Power(D(3), N()), D(2,2,4,1), N()), Sp, Iff, Sp,
        N(), Sp, Eq, Sp, D(1,8,0,4,3,2,0)));

    private static Formula Congruence(Formula a, Formula b, Formula modulus) => Seq(
        a, Sp, Equiv, Sp, b, Sp, Open, Mathrm, Grp(F.Id("mod")), Sp, modulus, Close);

    private static Formula N() => F.Id("n");
}
