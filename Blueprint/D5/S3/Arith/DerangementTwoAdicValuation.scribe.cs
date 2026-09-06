using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class DerangementTwoAdicValuationDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/Arith/DerangementTwoAdicValuation.";

    private static readonly LibraryNoteRef Miska =
        LibraryNoteRef.Create("D5/L/Arith/miska2016derangements");

    private static Formula Parenthesized(Formula value) =>
        F.Seq(F.Open, value, F.Close);

    private static Formula Naturals() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula Derangement(Formula index) =>
        F.Seq(F.Id("D"), F.Underscore, F.Grp(index));

    private static Formula Valuation(Formula value) =>
        F.Seq(F.Id("v"), F.Underscore, F.Grp(F.D(2)), Parenthesized(value));

    private static Formula Odd(Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("Odd")), Parenthesized(value));

    private static Formula Even(Formula value) =>
        F.Seq(F.Operatorname, F.Grp(F.Id("Even")), Parenthesized(value));

    private static Formula Power(Formula basis, Formula exponent) =>
        F.Seq(basis, F.Caret, F.Grp(exponent));

    private static Formula MainStatement(bool includePower = true)
    {
        var n = F.Id("n");
        var b = F.Id("b");
        var k = F.Id("k");
        var nMinusOne = F.Seq(n, F.Sp, F.Minus, F.Sp, F.D(1));

        var parity = F.Seq(
            F.Forall, F.Sp, n, F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            Odd(Derangement(n)), F.Sp, F.Leftrightarrow, F.Sp, Even(n));
        var exactValuation = F.Seq(
            F.Forall, F.Sp, n, F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            F.D(2), F.Sp, F.Le, F.Sp, n, F.Sp, F.Rightarrow, F.Sp,
            Valuation(Derangement(n)), F.Sp, F.Eq, F.Sp,
            Valuation(nMinusOne));
        if (!includePower)
        {
            return F.Disp(F.Seq(
                F.Begin, F.Grp(F.Id("gathered")),
                Parenthesized(parity), F.Sp, F.Land, F.RowBreak,
                Parenthesized(exactValuation), F.Dot,
                F.End, F.Grp(F.Id("gathered"))));
        }

        var powerDivisibility = F.Seq(
            F.Forall, F.Sp, n, F.Comma, F.Sp, b, F.Comma, F.Sp, k,
            F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            F.D(2), F.Sp, F.Le, F.Sp, n, F.Sp, F.Rightarrow, F.Sp,
            Derangement(n), F.Sp, F.Eq, F.Sp, Power(b, k), F.Sp,
            F.Rightarrow, F.Sp, k, F.Sp, F.Mid, F.Sp, Valuation(nMinusOne));

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            Parenthesized(parity), F.Sp, F.Land, F.RowBreak,
            Parenthesized(exactValuation), F.Sp, F.Land, F.RowBreak,
            Parenthesized(powerDivisibility), F.Dot,
            F.End, F.Grp(F.Id("gathered"))));
    }

    private static Formula ProgressionObstruction()
    {
        var t = F.Id("t");
        var b = F.Id("b");
        var k = F.Id("k");
        var index = F.Seq(F.D(4), F.Cdot, F.Sp, t, F.Sp, F.Plus, F.Sp, F.D(3));

        return F.Disp(F.Seq(
            F.Forall, F.Sp, t, F.Comma, F.Sp, b, F.Comma, F.Sp, k,
            F.Sp, F.InMacro, F.Sp, Naturals(), F.Comma, F.Sp,
            F.D(2), F.Sp, F.Le, F.Sp, k, F.Sp, F.Rightarrow, F.Sp,
            Derangement(index), F.Sp, F.Neq, F.Sp, Power(b, k), F.Dot));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Derangement parity and valuation exclude nontrivial powers at indices 3 mod 4.",
        H("Two-Adic Valuation of Derangement Numbers"),
        Blocks(
            Paragraph(Text(
                "Write D_n for Mathlib's natural number numDerangements n and v_2 for "
                + "padicValNat 2. The first declaration gives the literature parity and valuation "
                + "identity. The second states all three clauses of candidate theorem 4.102 "
                + "in one conjunction, adding the repository corollary on power exponents. "
                + "Natural subtraction is used in n - 1.")),
            Describe.Lean(
                DescribeId.Create("derangement-parity-and-exact-two-adic-valuation"),
                DeclarationHandle.Create(LeanPrefix + "numDerangements_two_adic_valuation"),
                H("Parity and exact two-adic valuation"),
                StatementSource.FromAuthor(MainStatement(includePower: false)),
                AssessedProvenance.FromLiterature(Miska),
                Blocks(
                    Paragraph(Text(
                        "These are exactly clauses (i)-(ii) of candidate theorem 4.102. "
                        + "The cited source states the valuation identity in Section 6.1, "
                        + "in the proof of Proposition 25; the parity law is its parity content, "
                        + "including D_0 = 1 and D_1 = 0. This attribution does not include "
                        + "the exponent-divisibility or perfect-power corollaries below.")),
                    Paragraph(Text(
                        "The Lean proof reconstructs the parity invariant by two-step induction "
                        + "through numDerangements_add_two. Consecutive derangement numbers then "
                        + "have odd sum. Factoring D_(m+2) as (m+1)(D_m+D_(m+1)) and cancelling "
                        + "the odd factor with the multiplicative p-adic valuation law yields the "
                        + "exact identity. The proof contains no numerical certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "derangement-parity-exact-two-adic-valuation-and-power-exponent-divisibility"),
                DeclarationHandle.Create(
                    LeanPrefix + "numDerangements_parity_valuation_and_power_exponent"),
                H("Parity, exact valuation, and exponent divisibility"),
                StatementSource.FromAuthor(MainStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Clauses (i)-(ii) are supplied by the preceding literature theorem. "
                        + "Clause (iii) is a repository corollary: if D_n = b^k, the power "
                        + "rule makes k divide v_2(D_n). The whole conjunction is repository-derived "
                        + "because the source attribution applies only to clauses (i)-(ii). "
                        + "The result includes b = 0 under Mathlib's convention "
                        + "padicValNat 2 0 = 0 and contains no numerical certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-adic-valuation-of-four-t-plus-two"),
                DeclarationHandle.Create(LeanPrefix + "padicValNat_two_four_mul_add_two"),
                H("Valuation at four times an index plus two"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("t"), F.Sp, F.InMacro, F.Sp, Naturals(),
                    F.Comma, F.Sp,
                    Valuation(F.Seq(F.D(4), F.Cdot, F.Sp, F.Id("t"), F.Sp,
                        F.Plus, F.Sp, F.D(2))), F.Sp, F.Eq, F.Sp, F.D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Four times a natural index plus two is twice an odd natural number."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create(
                    "derangements-at-indices-three-modulo-four-are-not-nontrivial-powers"),
                DeclarationHandle.Create(
                    LeanPrefix + "numDerangements_four_mul_add_three_ne_pow"),
                H("Indices three modulo four exclude nontrivial powers"),
                StatementSource.FromAuthor(ProgressionObstruction()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n = 4t + 3, natural subtraction gives n - 1 = 2(2t + 1), "
                        + "whose two-adic valuation is exactly one. The exponent-divisibility "
                        + "clause of the preceding declaration would force every exponent k of "
                        + "a power representation to divide one, contradicting 2 <= k. This is "
                        + "the directed companion 4.103 -> 4.102 (consumer -> prerequisite).")),
                    Paragraph(Text(
                        "Zhi-Wei Sun's 2025 OEIS A000166 comment conjectures that, for n > 2, "
                        + "only D_4 = 3^2 is a perfect power. This repository-derived theorem "
                        + "settles only the infinite progression n congruent to 3 modulo 4; it "
                        + "does not prove that conjecture, and D_4 remains outside its scope."))),
                DescribeRole.Theorem))));
}
