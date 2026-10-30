using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class CdsoCapacityCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/CdsoCapacityCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A capacity certificate for the actual marginals of one finite subset law.",
        H("CDSO capacity residual on the entire subset domain"),
        Blocks(
            Paragraph(Text(
                "The carrier is Fin(a+2), with natural a at least 4096. This represents exactly the " +
                "integer domain a>=4096. The real parameter satisfies 0<delta<=1/a, including delta=1/a. " +
                "Set r=a+1, s=a+2, c=2a+1 and tau=3(2a+3)delta/r^2. Atom(a) is the type of all nonempty " +
                "finite subsets of this carrier. No atom is removed because its mass is zero.")),
            Describe.Lean(DescribeId.Create("dense-law"),
                DeclarationHandle.Create(Prefix + "DenseLaw"), H("One dense subset law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A DenseLaw consists of nonnegative real masses x(T) on every nonempty T, of total one, " +
                    "with sum_T x(T)|T|=a+1-delta. Its actual marginal y(i) is sum_T 1_(i in T)x(T), and " +
                    "each marginal is at least tau. Marginals are derived from this same mass function; " +
                    "they are not independent input data. All cardinalities 1 through s, disconnected " +
                    "incidence supports, zero masses and nonsymmetric laws remain in scope."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("energy"),
                DeclarationHandle.Create(Prefix + "energy"), H("Native energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "energy(x)=sum_T x(T)|T|^2 sum_(i in T) y(i)^(-2), with y=marginal(x). This is H in " +
                    "Definition 1.1 of CDSO capacity crossovers and rare phases. That source identifies " +
                    "H=2J_s and B=2F_r(q) through its cited common-array parent model. This module proves " +
                    "finite-law statements; it supplies no additional finite-graph realization bridge. " +
                    "The source reference moment Z=delta*a^3+(1-delta)r^3 is not assumed to be the third " +
                    "moment of an arbitrary admissible law."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("capacity-certificate"),
                DeclarationHandle.Create(Prefix + "capacity_certificate"), H("Pointwise certificate and entire zero set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every DenseLaw in the stated parameter range whose actual marginals are in " +
                        "nonincreasing order, let t be label 2, the third label in zero-based indexing. Put " +
                        "alpha(i)=y(i)^(-2), W=sum_i alpha(i), omega=alpha(t), b(i)=c*max(omega-alpha(i),0), " +
                        "and W_T=sum_(i in T) alpha(i). For every nonempty subset T, including zero-mass atoms, " +
                        "R(T)=(r-|T|)[c(W-2omega)-(r+|T|)W_T]+sum_(i outside T)b(i) is nonnegative.")),
                    Paragraph(Text(
                        "Its full zero set is exactly the union of these two cases: |T|=r, the complement " +
                        "is {i}, and y(i)<=y(t); or |T|=a, the complement is {i,j} with i different from j, " +
                        "and both y(i) and y(j) are at least y(t). All ties are included.")),
                    Paragraph(Text(
                        "The mean and ordering give q<=2+a*y(t), hence y(t)>=(a-1-delta)/a>=1-2/a. " +
                        "The proof obtains alpha(i)>=1 and 1<=omega<16/15. At |T|=r, R is the omitted " +
                        "positive part. At |T|=a, reflection of the positive part gives c times the sum " +
                        "of max(alpha(i)-omega,0) over omitted indices. At |T|=s, R=2W+2c*omega>0. " +
                        "For |T|<a, the omitted cardinality is between 3 and s-1. The residual bracket is " +
                        "at least (41a-2)/15>0. These four cases exhaust the full subset domain."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("same-law-bound"),
                DeclarationHandle.Create(Prefix + "same_law_bound"), H("Exact same-law decomposition and support equality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same complete parameter and law hypotheses, define L=r^2 sum_i 1/y(i) " +
                        "-c*delta*(W-2omega)-sum_i(1-y(i))*b(i). Then H=L+sum_T x(T)R(T), so H>=L. " +
                        "Moreover H=L if and only if R(T)=0 for every T with x(T)>0. Zero masses impose " +
                        "no support equality condition.")),
                    Paragraph(Text(
                        "Finite sums are interchanged to identify E[sum_(i in T)h(i)] with sum_i h(i)y(i). " +
                        "The complement identity uses P(i outside T)=1-y(i), and the cardinality term uses " +
                        "E[r-|T|]=delta. All three expectations use the original mass function. The " +
                        "existing Finset.sum_eq_zero_iff_of_nonneg supplies the final support argument."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The grouped functions F0, F1 and their strict Jensen equality consequences in Lemma 16.2 " +
                "require additional statements beyond the pointwise and expectation conclusions described here. " +
                "The present statements do not assert convexity of H as a function of its law, a fixed-budget " +
                "finite-graph realization, or a literature priority claim."))
        )));
}
