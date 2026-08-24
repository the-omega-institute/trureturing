using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.PrimeRefinement;

internal sealed class FinitePrimeExtractionZeroPersistenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/PrimeRefinement/FinitePrimeExtractionZeroPersistence."
            + "finite_prime_extraction_preserves_zeta_zero";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A critical-strip zeta zero persists after any finite extraction of prime Euler factors.",
        H("Finite Prime Extraction Zero Persistence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-prime-extraction-preserves-zeta-zero"),
            DeclarationHandle.Create(Declaration),
            H("Finite prime extraction preserves a zeta zero"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public statement constructs the analytic residual directly as zeta at "
                        + "rho multiplied by the finite product of local factors. The finite set, "
                        + "the primality of each member, both open-strip bounds, and the zeta-zero "
                        + "hypothesis are all explicit.")),
                Paragraph(Text(
                    "The proof applies the frozen finite-prime-modification zero-set theorem. "
                        + "Unfolding that repository modification and its finite Euler product "
                        + "turns division by the product of inverse denominators into the displayed "
                        + "product of denominators."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Weil/PrimeAddress/PrimeAddress"))]));

    private static Formula TheoremFormula()
    {
        Formula rho = Rho;
        Formula primes = F.Id("S");
        Formula prime = F.Id("p");
        Formula zetaAtRho = Seq(Zeta, Open, rho, Close);
        Formula realPart = Seq(Re, Open, rho, Close);
        Formula finitePrimeSet = Seq(
            primes, Sp, Subset, Underscore, Grp(Mathrm, Grp(F.Id("fin"))), Sp,
            Mathbb, Grp(F.Id("N")));
        Formula primeMembership = Seq(
            Forall, Sp, prime, Sp, InMacro, Sp, primes, Comma, Sp,
            Operatorname, Grp(F.Id("Prime")), Open, prime, Close);
        Formula localPower = new Formula.Power(
            Seq(Open, prime, Close),
            Seq(Minus, rho));
        Formula finiteProduct = Seq(
            Prod, Underscore, Grp(prime, Sp, InMacro, Sp, primes), Sp,
            Open, D(1), Sp, Minus, Sp, localPower, Close);
        Formula hypotheses = Seq(
            D(0), Sp, Lt, Sp, realPart, Sp, Land, Sp,
            realPart, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            zetaAtRho, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            primeMembership);
        Formula residual = Seq(zetaAtRho, Sp, Cdot, Sp, finiteProduct);

        return Disp(Seq(
            Forall, Sp, rho, Sp, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
            Forall, Sp, finitePrimeSet, Comma, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            residual, Sp, Eq, Sp, D(0), Dot));
    }
}
