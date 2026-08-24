using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PadicPrecisionBlindSpotDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Arith/Congruence/PadicPrecisionBlindSpot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power readings agree through the p-adic valuation of a nonzero difference, "
            + "and its successor is the first precision that distinguishes the integers.",
        H("The p-adic Precision Blind Spot"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reading-agreement-is-bounded-by-the-p-adic-valuation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "precision_reading_eq_iff_le_padicValInt"),
                H("Reading agreement lasts exactly through the p-adic valuation"),
                StatementSource.FromAuthor(AgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a prime p and two distinct integers x and y. Their precision-k "
                            + "readings are their residues modulo p^k. These readings agree "
                            + "exactly when k is at most the p-adic valuation of x - y.")),
                    Paragraph(Text(
                        "Thus the valuation measures the complete blind range of the prime-power "
                            + "readout: every precision through that value hides the nonzero "
                            + "difference, while every larger precision detects it."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("valuation-successor-is-the-first-distinguishing-precision"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "first_distinguishing_precision"),
                H("The valuation successor is the first distinguishing precision"),
                StatementSource.FromAuthor(FirstDistinguishingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p and distinct integers x and y, one more than the p-adic "
                            + "valuation of x - y is a precision at which their prime-power "
                            + "readings differ.")),
                    Paragraph(Text(
                        "Every smaller precision is at most the valuation and therefore gives "
                            + "equal readings. The successor consequently belongs to the set of "
                            + "distinguishing precisions and is no greater than any other member, "
                            + "so it is the least such precision."))),
                DescribeRole.Theorem))));

    private static Formula Reading(Formula prime, Formula precision, Formula value) =>
        Call("precisionReading", prime, precision, value);

    private static Formula Valuation(Formula prime, Formula difference) =>
        Call("padicValInt", prime, difference);

    private static Formula AgreementFormula()
    {
        Formula prime = F.Id("p");
        Formula precision = F.Id("k");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula difference = Subtract(left, right);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Comma, Sp, precision, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("Z")), Comma, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Land, Sp, left, Sp, Neq, Sp, right, Close,
            Sp, Rightarrow, Sp,
            Open, Reading(prime, precision, left), Sp, Eq, Sp,
            Reading(prime, precision, right), Close,
            Sp, Iff, Sp, precision, Sp, Leq, Sp,
            Valuation(prime, difference), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FirstDistinguishingFormula()
    {
        Formula prime = F.Id("p");
        Formula precision = F.Id("k");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula difference = Subtract(left, right);
        Formula distinguishingPrecisions = Seq(
            OpenBrace, precision, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
            Mid, Sp, Reading(prime, precision, left), Sp, Neq, Sp,
            Reading(prime, precision, right), CloseBrace);
        Formula firstDistinguishing = Seq(
            Valuation(prime, difference), Sp, Plus, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("Z")), Comma, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Land, Sp, left, Sp, Neq, Sp, right, Close,
            Sp, Rightarrow, Sp,
            Call("IsLeast", distinguishingPrecisions, firstDistinguishing), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
