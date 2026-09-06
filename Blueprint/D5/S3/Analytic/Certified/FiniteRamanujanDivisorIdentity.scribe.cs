using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Certified;

internal sealed class FiniteRamanujanDivisorIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Certified/FiniteRamanujanDivisorIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized sum of finite Ramanujan phases over the divisors of d "
            + "is the indicator that d divides n.",
        H("Finite Ramanujan Divisor Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-ramanujan-sum"),
                DeclarationHandle.Create(Prefix + "ramanujanSum"),
                H("The finite Ramanujan phase sum"),
                StatementSource.FromAuthor(RamanujanSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural q and n, ramanujanSum q n is exactly the finite sum of "
                        + "exp(2 pi i a n / q) over natural residues a below q that are "
                        + "coprime to q. In particular, the phase carrier is not replaced "
                        + "by an arithmetically equivalent definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-divisor-indicator"),
                DeclarationHandle.Create(Prefix
                    + "divisorIndicator_eq_normalized_sum_ramanujanSum"),
                H("Normalized Ramanujan sums reconstruct the divisor indicator"),
                StatementSource.FromAuthor(DivisorIndicatorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural d and natural n, the indicator of d "
                            + "dividing n equals one over d times the sum of c_q(n) over "
                            + "all positive divisors q of d. This is formula (4) in the "
                            + "finite reconstruction argument.")),
                    Paragraph(Text(
                        "The proof first constructs the coprime-index bijection from the "
                            + "source phases to primitive q-th roots. Primitive roots of "
                            + "all orders q dividing d partition the d-th roots of unity; "
                            + "the complete root sum is then d when d divides n and zero "
                            + "otherwise.")),
                    Paragraph(Text(
                        "This module does not prove the von Mangoldt equality, the weighted "
                            + "finite phase expansion, or independence of that expansion "
                            + "from tau. Those remain separate obligations."))),
                DescribeRole.Theorem))));

    private static Formula RamanujanSumFormula()
    {
        Formula q = F.Id("q"), n = F.Id("n"), a = F.Id("a");
        Formula index = Seq(
            D(0), Sp, Leq, Sp, a, Sp, Lt, Sp, q, Comma, Sp,
            Call("Coprime", a, q));
        Formula phase = Call("exp", Multiply(
            Multiply(Multiply(D(2), Pi), F.Id("i")),
            new Formula.Fraction(Multiply(a, n), q)));
        Formula sum = Seq(Sum, Underscore, Grp(index), Sp, phase);

        return Disp(Seq(
            Forall, Sp, q, Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Call("ramanujanSum", q, n), Sp, Eq, Sp, sum, Dot));
    }

    private static Formula DivisorIndicatorFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), q = F.Id("q");
        Formula divides = new Formula.Relation(
            d, FormulaRelationOperator.Divides, n);
        Formula divisorIndex = new Formula.Relation(
            q, FormulaRelationOperator.Divides, d);
        Formula ramanujan = Call("ramanujanSum", q, n);
        Formula divisorSum = Seq(Sum, Underscore, Grp(divisorIndex), Sp, ramanujan);
        Formula indicator = new Formula.Subscript(
            Seq(Mathbf, Grp(D(1))), Grp(OpenBrace, divides, CloseBrace));
        Formula normalized = Multiply(new Formula.Fraction(D(1), d), divisorSum);

        return Disp(Seq(
            Forall, Sp, d, Comma, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(0), Sp, Lt, Sp, d, Sp, Rightarrow, Sp,
            indicator, Sp, Eq, Sp, normalized, Dot));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
