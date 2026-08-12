using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class EisensteinCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minus three is a quadratic residue mod an odd prime p not 3 iff p is one mod three.",
        H("The Discriminant Minus-Three Splitting Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discriminant-neg-three-quadratic-residue-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Splitting/EisensteinCriterion.neg_three_isSquare_iff"),
                H("Minus three is a residue mod p iff p is one mod three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Sp, Operatorname, Grp(F.Id("prime")), Comma, Sp,
                    F.Id("p"), Neq, Sp, D(2), Comma, Sp, F.Id("p"), Neq, Sp, D(3), Sp,
                    Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("IsSquare")), Open, Minus, D(3), Sp,
                    Colon, Sp, F.Id("ZMod"), Sp, F.Id("p"), Close, Sp,
                    Iff, Sp, F.Id("p"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(3), Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an odd prime p not equal to 3, the field element -3 in ZMod p is a quadratic "
                        + "residue — a square in ZMod p — if and only if p is congruent to 1 modulo 3. "
                        + "Since -3 is the discriminant of x^2 + x + 1, this being a square mod p is "
                        + "exactly the condition for p to split in the Eisenstein integers. Both p not 2 "
                        + "and p not 3 are required: -3 is congruent to 1 (a square) mod 2 yet 2 is not "
                        + "1 mod 3, and -3 is congruent to 0 mod 3.")),
                    Paragraph(Text(
                        "The proof runs through the Legendre symbol. Writing -3 as (-1) times 3, the -1 "
                        + "factor contributes the character chi-4 of p, equal to (-1) raised to p/2, and "
                        + "quadratic reciprocity between p and 3 cancels that sign, reducing the residue "
                        + "condition (-3 / p) = 1 to (p / 3) = 1. Casting p modulo 3 and splitting the two "
                        + "nonzero residues — 1 is a residue, 2 is a non-residue — finishes the proof.")),
                    Paragraph(Text(
                        "Only this residue criterion — the central discriminant-minus-three clause — is "
                        + "recorded here. The dyadic 2-adic clause, that 3 k^2 + 1 is an Eisenstein norm "
                        + "for odd k, and the ladder-factory corollary of the wider result are not covered "
                        + "by this statement."))),
                DescribeRole.Theorem))));
}
