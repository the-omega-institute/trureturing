using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Precision;

internal sealed class PrimePowerPrecisionBlindSpotDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Precision/PrimePowerPrecisionBlindSpot."
            + "prime_power_precision_blind_spot";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed prime, the valuation of a nonzero integer difference exactly controls "
            + "both the blind residue precisions and the first precision that separates it.",
        H("Prime-Power Precision Blind Spot"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-power-agreement-and-first-separating-precision"),
            DeclarationHandle.Create(Declaration),
            H("The valuation controls agreement and the first distinguishing precision"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a prime p, a positive natural precision k, and distinct integers x and y. "
                        + "The precision reading is the residue modulo p^k. The two readings "
                        + "agree exactly when k does not exceed the p-adic valuation of x - y.")),
                Paragraph(Text(
                    "The named firstDistinguishingPrecision is the source's kappa_p(x,y): "
                        + "the least positive precision whose readings differ. Its value is "
                        + "exactly one more than that same valuation."))),
            DescribeRole.Theorem))));

    private static Formula Reading(Formula prime, Formula precision, Formula value) =>
        Call("precisionReading", prime, precision, value);

    private static Formula Valuation(Formula prime, Formula difference) =>
        Call("padicValInt", prime, difference);

    private static Formula TheoremFormula()
    {
        Formula prime = F.Id("p");
        Formula precision = F.Id("k");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula difference = Subtract(left, right);
        Formula agreement = Seq(
            Open, Reading(prime, precision, left), Sp, Eq, Sp,
            Reading(prime, precision, right), Close,
            Sp, Iff, Sp, precision, Sp, Leq, Sp, Valuation(prime, difference));
        Formula firstPrecision = Seq(
            Call("firstDistinguishingPrecision", prime, left, right),
            Sp, Eq, Sp, Valuation(prime, difference), Sp, Plus, Sp, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Comma, Sp, precision, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            left, Comma, Sp, right, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("Z")), Comma, RowBreak, Grp(),
            Open, Call("Prime", prime), Sp, Land, Sp,
            D(1), Sp, Leq, Sp, precision, Sp, Land, Sp,
            left, Sp, Neq, Sp, right, Close,
            Sp, Rightarrow, Sp,
            Open, agreement, Close, Sp, Land, RowBreak, Grp(),
            Open, firstPrecision, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
