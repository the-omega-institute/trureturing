using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Derangements;

internal sealed class DerangementTwoAdicValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Derangements/DerangementTwoAdicValuation.";

    private static readonly LibraryNoteRef Miska =
        LibraryNoteRef.Create("D5/L/ArithSums/miska2016derangements");
    private static readonly LibraryNoteRef Oeis =
        LibraryNoteRef.Create("D5/L/ArithSums/oeis2025a000166");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derangement numbers have index-controlled parity and exact binary valuation.",
        H("Parity and Binary Valuation of Derangement Numbers"),
        Blocks(
            Paragraph(Text(
                "Write D_n for Mathlib's numDerangements n, and write v_2 for "
                    + "padicValNat 2. All variables below range over natural numbers.")),
            Describe.Lean(
                DescribeId.Create("derangement-parity"),
                DeclarationHandle.Create(Prefix + "numDerangements_odd_iff_even"),
                H("Parity alternates with the index"),
                StatementSource.FromAuthor(ParityFormula()),
                AssessedProvenance.FromRepo(Miska, Oeis),
                Blocks(Paragraph(Text(
                    "The initial values are D_0=1 and D_1=0. For the induction step, "
                        + "D_(n+2)=(n+1)(D_n+D_(n+1)). If n is even, the multiplier and "
                        + "the sum are odd; if n is odd, the multiplier is even. Thus D_n "
                        + "is odd exactly when n is even."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-binary-valuation"),
                DeclarationHandle.Create(Prefix + "padicValNat_numDerangements"),
                H("The exact binary valuation"),
                StatementSource.FromAuthor(ValuationFormula()),
                AssessedProvenance.FromRepo(Miska, Oeis),
                Blocks(Paragraph(Text(
                    "For n at least two, D_(n-2) and D_(n-1) have opposite parity, so "
                        + "their sum is odd and has binary valuation zero. Applying the "
                        + "valuation product rule to D_n=(n-1)(D_(n-2)+D_(n-1)) leaves "
                        + "exactly the valuation of n-1. Miska records the same identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("power-exponent-divisibility"),
                DeclarationHandle.Create(
                    Prefix + "exponent_dvd_padicValNat_sub_one_of_numDerangements_eq_pow"),
                H("A power exponent divides the preceding-index valuation"),
                StatementSource.FromAuthor(PowerFormula()),
                AssessedProvenance.FromRepo(Miska, Oeis),
                Blocks(Paragraph(Text(
                    "Substitute D_n=b^k into the exact valuation identity. The valuation "
                        + "of b^k is k times the valuation of b, so k divides v_2(n-1). "
                        + "This also includes b=0 under padicValNat's value zero at zero. "
                        + "Sun's OEIS comment gives a broader perfect-power observation checked "
                        + "through n=1000; the universal divisibility statement here is derived "
                        + "from the preceding theorem."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Dn(Formula n) => new Formula.Subscript(V("D"), n);
    private static Formula Val(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("v"), D(2)), [n]);
    private static Formula Odd(Formula n) => new Formula.Apply(V("Odd"), [n]);
    private static Formula Even(Formula n) => new Formula.Apply(V("Even"), [n]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ParityFormula()
    {
        Formula n = V("n");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Nat(), Comma, Sp,
            Odd(Dn(n)), Sp, Iff, Sp, Even(n)));
    }

    private static Formula ValuationFormula()
    {
        Formula n = V("n");
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Nat(), Comma, Sp,
            LessEqual(D(2), n), Sp, Rightarrow, Sp,
            Equal(Val(Dn(n)), Val(Subtract(n, D(1))))));
    }

    private static Formula PowerFormula()
    {
        Formula n = V("n");
        Formula b = V("b");
        Formula k = V("k");
        Formula hypotheses = And(
            LessEqual(D(2), n),
            Equal(Dn(n), new Formula.Power(b, k)));
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, b, Comma, Sp, k,
            Sp, InMacro, Sp, Nat(), Comma, Sp,
            Implies(hypotheses, Divides(k, Val(Subtract(n, D(1)))))));
    }
}
