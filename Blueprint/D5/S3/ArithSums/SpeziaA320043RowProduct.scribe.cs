using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SpeziaA320043RowProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/SpeziaA320043RowProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The terms of row n of A320043 multiply to B(n+1)³, where B(N)=∏ k/gcd(k,N); "
            + "B(p)=(p−1)! at primes.",
        H("The row product of A320043"),
        Blocks(
            Describe.Lean(DescribeId.Create("spezia-a320043-row-product-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Row product, diagonal term and prime values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let X(n,k)=(n+1−k)²k/gcd(n+1−k,k)³ be the k-th term of row n of OEIS "
                    + "A320043 and B(N)=∏_{k=1}^{N} k/gcd(k,N), the row product of A322550 "
                    + "(Spezia). Then X(2m−1,m)=1 for m ≥ 1; for n ≥ 1, "
                    + "∏_{k=1}^{n} X(n,k)=B(n+1)³, equivalently the positive real cube roots "
                    + "of the terms multiply to B(n+1); and B(p)=(p−1)! for every prime p. Put "
                    + "N=n+1 and g=gcd(k,N). Since gcd(N−k,k)=gcd(N−k,N)=g, each term splits "
                    + "exactly as X(n,k)=((N−k)/gcd(N−k,N))²·(k/g). The reflection k ↦ N−k is a "
                    + "bijection of {1,…,n}, so the first factors multiply to the same value "
                    + "P=∏_{k=1}^{n} k/gcd(k,N) as the second ones, giving P³; and B(N)=P because "
                    + "the term k=N equals 1. For a prime p, gcd(k,p)=1 when k<p, so "
                    + "B(p)=(p−1)!. This is Corollary 6 of H. Ma and W. Zhang's note on A320043 "
                    + "(DOI 10.5281/zenodo.24058057); the prime case is due to Steinerberger, "
                    + "and related divisor-product formulas to Křížek and Oudra (A119619)."))),
                DescribeRole.Theorem))));
}
