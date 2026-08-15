using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class FourierMatrixDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic defect of a Fourier matrix is supplied by its nontrivial divisors.",
        H("Fourier-Matrix Defect and Divisor Supply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourier-matrix-defect-factor-supply"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/FourierMatrixDefect."
                    + "fourier_defect_factor_supply"),
                H("Fourier-matrix defect is supplied by nontrivial divisors"),
                StatementSource.FromAuthor(FactorSupplyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For n at least two, define the arithmetic Fourier defect as the sum "
                        + "of gcd(n,k)-1 over 1 <= k < n. Grouping residues by their gcd with "
                        + "n shows that a divisor d contributes phi(d) copies of n/d-1 after "
                        + "the divisor involution d maps to n/d. Removing k=0 on the residue "
                        + "side cancels the d=1 contribution on the divisor side.")),
                    Paragraph(Text(
                        "The source's divisor sum is read over nontrivial divisors. This is the "
                        + "only reading compatible with its same-clause assertion that the defect "
                        + "vanishes at prime orders: including d=1 would contribute n-1. The Lean "
                        + "statement records both the exact factor-supply formula and the prime "
                        + "vanishing criterion, with the lower bound n >= 2 explicit.")),
                    Paragraph(Text(
                        "The pinned library search found Nat.totient_div_of_dvd as the exact gcd "
                        + "fiber count and Nat.sum_div_divisors as the exact divisor reindexing; "
                        + "both are imported and applied. Loogle found no theorem matching the "
                        + "complete identity, LeanSearch was unavailable locally, and repository "
                        + "searches found no declaration with this statement.")),
                    Paragraph(Text(
                        "The converse is substantive: if n is composite, mathlib supplies a proper "
                        + "divisor d with 2 <= d < n. Its k=d summand is d-1 > 0, contradicting "
                        + "zero defect. For prime n the divisor set is exactly {1,n}, and the sole "
                        + "nontrivial-divisor summand vanishes."))),
                DescribeRole.Theorem))));

    private static Formula Defect(Formula n) =>
        Seq(Operatorname, Grp(F.Id("defect")), Open,
            F.Id("F"), Underscore, Grp(n), Close);

    private static Formula FactorSupplyFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula defect = Defect(n);
        Formula divisorCondition = Grp(
            d, Mid, Sp, n, Comma, Sp, d, Gt, D(1));
        Formula supply = Seq(
            Sum, Underscore, divisorCondition, Sp,
            Varphi, Open, d, Close,
            Open, Frac, Grp(n), Grp(d), Minus, D(1), Close);
        return Disp(Seq(
            Forall, Sp, n, InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            n, Geq, D(2), Sp, Rightarrow, Sp,
            Left, Open,
            defect, Sp, Eq, Sp, supply, Sp, Land, Sp,
            Open, defect, Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            Operatorname, Grp(F.Id("Prime")), Open, n, Close, Close,
            Right, Close, Dot));
    }
}
