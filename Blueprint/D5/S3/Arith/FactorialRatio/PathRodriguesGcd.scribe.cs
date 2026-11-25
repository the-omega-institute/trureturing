using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class PathRodriguesGcdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/PathRodriguesGcd.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact signed path factorial moments and their primitive gcd",
        H("The path Rodrigues gcd"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-path-moment"),
                DeclarationHandle.Create(Prefix + "rawMoment_eq"),
                H("Signed raw factorial moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n edges, n+1 vertices, natural s and order k<=s, the raw moment "
                    + "is (-1)^(nk)(s!)^(n+1). An edge allocates j derivatives to its source "
                    + "and k-j to its target. Surviving allocations have total local load at "
                    + "most s at every vertex, with coefficient the product of local multinomials. "
                    + "After factorial weighting, each edge contributes a signed binomial "
                    + "transition. Its row sum is (-1)^k by finite differences. Infeasible "
                    + "allocations contribute zero to the extended transition sum, which "
                    + "factors recursively along the path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("primitive-path-moment"),
                DeclarationHandle.Create(Prefix + "primitiveMoment_eq"),
                H("Signed primitive factorial moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For k<=s the coefficient content C(n,s,k) is the gcd of all surviving "
                    + "multinomial coefficients and divides F(n,s)=(s!)^(n+1). Dividing each "
                    + "coefficient by its content gives primitive moment (-1)^(nk)B(n,s,k), "
                    + "where B=F/C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("path-prime-witness"),
                DeclarationHandle.Create(Prefix + "B_factorization_primeOrder"),
                H("Exact prime-specific order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p and natural n,s, take k=p^floor(log_p(s+1))-1. "
                    + "This order is at most s. The two loads of each edge sum to k, "
                    + "so modulo each positive power q of p dividing k+1 their residues "
                    + "sum to q-1. The resulting floor bound on all coefficient denominators "
                    + "forces the p-adic valuation of B(n,s,k) to equal that of "
                    + "A(n,s)=tailLCM((n+1)s+n,n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-path-rodrigues-gcd"),
                DeclarationHandle.Create(Prefix + "exact_path_rodrigues_gcd"),
                H("Exact primitive path gcd"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural vertex count r>=2 and natural s, the gcd of "
                    + "B(r-1,s,k) over 0<=k<=s equals tailLCM(r(s+1)-1,r-1). "
                    + "All surviving exponent tuples have total degree rs. The rank-one "
                    + "factorial-product gcd therefore divides every primitive magnitude. "
                    + "The prime-specific order attains its valuation at each prime, "
                    + "giving the reverse divisibility. The signed moment identity and "
                    + "the gcd are proved for the explicit finite allocation family."))),
                DescribeRole.Theorem))));
}
