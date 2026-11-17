using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormCCNRDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormCCNR.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-dimensional CCNR specialization without filter normal form", H("Equal-dimensional CCNR specialization without filter normal form"), Blocks(
            Entry("normalized-identity-singular-lower", "normalized_identity_singular_lower", "normalized identity singular lower",
                "For every positive equal local dimension and actual complex trace-one density, normalized identities have unit Hermitian-coordinate norms in every pair of complete trace-product-normalized local bases. Their actual correlation pairing is 1/d, proving the largest native singular value is at least 1/d. This is the normalized application of Li, Poon and Sze (2011), Lemma 2.1; separability and FNF are not premises.", DescribeRole.Theorem),
            Entry("equal-dimensional-ccnr", "equal_dimensional_ccnr", "equal dimensional ccnr",
                "For every integer d at least two and d <= h <= d squared, every actual density satisfying CCNR (the complete descending correlation singular-value sum is at most one) obeys M(h,infinity) <= (1/d)*((d-1)/(d*(h-1)))^(h-1), exactly the original B(d,d,h). The proof uses the actual compound product correspondence, AM-GM on the remaining h-1 singular values and monotonicity on the full real interval [1/d,1]. Potentially entangled CCNR states are included. No hidden separability or FNF restriction is introduced.", DescribeRole.Theorem),
            Entry("equal-dimensional-ccnr-full", "equal_dimensional_ccnr_full", "equal dimensional ccnr full",
                "At full smaller-side order h=d squared the increasing compound has one row, so the same bound holds for every actual finite Schatten p >= 1 and infinity, including rank-deficient states. Intermediate finite p, h<d, and unequal general dimensions remain outside this conclusion. In the stated operator range this criterion detects no entanglement beyond CCNR. The corresponding equal-dimensional p=1 comparison is already Li, Poon and Sze (2011), Theorem 2.4.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
