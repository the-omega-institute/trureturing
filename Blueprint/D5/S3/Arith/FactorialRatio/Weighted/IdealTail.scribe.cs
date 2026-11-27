using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Weighted;

internal sealed class IdealTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Weighted/IdealTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual bounded-norm ideal intersections give the residue-weighted factorial tail.",
        H("The bounded-norm ideal tail"),
        Blocks(
            Paragraph(Text(
                "Let K be a number field and O its ring of integers. For t a natural number, "
                + "intersect all nonzero integral ideals of O whose absolute norm is at most t. "
                + "Unique factorization of ideals determines this intersection prime by prime. "
                + "At a nonzero prime ideal P its exponent is floor(log base NP of t). "
                + "This description identifies the norm of the tail product with the weighted "
                + "tail defined by the actual residue degrees.")),
            Describe.Lean(
                DescribeId.Create("ideal-intersection"),
                DeclarationHandle.Create(Prefix + "idealIntersection"),
                H("Intersection over a bounded norm fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define J_K(t) as the intersection of every ideal I with I nonzero and NI<=t. "
                    + "The norm fiber is finite. At t=0 there are no such ideals, so J_K(0)=O. "
                    + "For positive t the unit ideal is among the factors; it imposes no additional restriction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ideal-tail"),
                DeclarationHandle.Create(Prefix + "idealTail"),
                H("Product of bounded-norm intersections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiply J_K(floor(H/k)) over M<k<=H. The product is the unit ideal when M>=H. "
                    + "Its absolute norm is denoted T_K. The definition uses multiplication and "
                    + "intersection in the actual ideal lattice of O."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ideal-intersection-tail"),
                DeclarationHandle.Create(Prefix + "ideal_intersection_tail"),
                H("Logarithmic ideal exponents and the exact tail norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every t the bounded-norm family is finite and J_K(t) is nonzero. "
                        + "For every nonzero prime ideal P, its multiplicity in J_K(t) is Nat.log(NP,t), "
                        + "with Nat.log(NP,0)=0. Moreover J_K(0)=O, and "
                        + "N(product over M<k<=H of J_K(floor(H/k))) equals weightedTail(H,M,c), "
                        + "where c(p,j)=sum of f(P) over P above p with f(P) dividing j+1. "
                        + "The index j starts at zero, so it represents p^(j+1). No restriction M<=H is needed for this identity.")),
                    Paragraph(Text(
                        "To identify the intersection, put L=floor(log base NP of t). For t>0, "
                        + "the ideal P^L has norm (NP)^L<=t, so J_K(t) is contained in P^L. "
                        + "Conversely, if I has norm at most t and P occurs to exponent v in I, "
                        + "then (NP)^v divides NI and hence (NP)^v<=t. Thus v<=L. "
                        + "The finite product of all these prime powers is contained in every I. "
                        + "Distinct prime ideals are coprime, so their product is their intersection. "
                        + "These two inclusions identify J_K(t), prove it nonzero, and give the exact multiplicities.")),
                    Paragraph(Text(
                        "In the tail product the exponent of P is sum over M<k<=H of log_(NP)(floor(H/k)). "
                        + "Count each power (NP)^a by the indices k for which k<=(H/(NP)^a). "
                        + "Exchanging the finite sums gives sum over a>=1 of max(0,floor(H/(NP)^a)-M). "
                        + "For P above p, NP=p^f(P). Reindex by multiples of f(P), multiply by f(P) "
                        + "when taking the absolute norm, and sum over P above p. The resulting coefficient "
                        + "at p^(j+1) is exactly c(p,j). Prime powers beyond H have zero contribution.")),
                    Paragraph(Text(
                        "Combining the norm identity with number_field_norm_and_complement gives the "
                        + "composition gcd for the norms of the Euler factorial ideals: it is precisely T_K. "
                        + "The complementary gcd is tailLCM(H,M)^d/T_K, where d=[K:Q] and M<=H. "
                        + "The weighted theorem supplies common witnesses for each rational prime, including "
                        + "all prime ideals above that prime. The argument takes the norm of the ideal tail "
                        + "after identifying its prime-ideal exponents; it does not commute the norm with a gcd.")),
                    Paragraph(Text(
                        "The factorial ideal used here is the explicit full-ring prime-ideal Euler product. "
                        + "An identification with an independently defined factorial from p-orderings or "
                        + "integer-valued polynomials requires that construction and its local exponent theorem. "
                        + "This theorem establishes the actual ideal-intersection tail and does not assert that separate correspondence."))),
                DescribeRole.Theorem))));
}
