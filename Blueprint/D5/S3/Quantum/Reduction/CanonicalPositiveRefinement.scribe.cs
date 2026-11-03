using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class CanonicalPositiveRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every original positive record of a canonical filter has normalized block scalars and is completely positive.",
        H("CanonicalPositiveRefinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-refinement-coefficients"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CanonicalPositiveRefinement.canonical_refinement_coefficients"),
                H("The exact formula on the original labels and centers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A be an arbitrary finite type of original fine records, B an arbitrary finite decidable type of original centers, and d(b) arbitrary finite decidable coordinate types. Let E(b) be PSD matrices, and S(a) complex linear endomorphisms of the product of the original matrix blocks. Assume ordinary componentwise positivity of each S(a) and the identity sum_a S(a)(X)(b)=sqrt(E(b)) X(b) sqrt(E(b)) for every complex input X and b. Then there are real coefficients c(a,b) in [0,1], whose sum over the same original labels a is one whenever E(b) is nonzero, with S(a)(X)(b)=c(a,b) sqrt(E(b)) X(b) sqrt(E(b)) for every a, X and b. Thus there is no off-center output, and every branch vanishes on each zero effect block. Dimensions may differ and effects may be singular. No CP or Kraus representation of a fine record is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-refinement-completely-positive"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/CanonicalPositiveRefinement.canonical_refinement_completely_positive"),
                H("All finite amplifications of the actual records are positive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under precisely the preceding assumptions, for each original a, every natural k, and every componentwise PSD input Z(b) indexed by d(b) times Fin(k), the matrix with (i,j) entry S(a)(z maps to the matrix (r,s) maps to Z(z)((r,i.second),(s,j.second)))(b)(i.first,j.first) is PSD in every output block b. This is the literal finite-ancilla amplification of each actual original direct-sum map. The scalar formula identifies it with c(a,b) times congruence by sqrt(E(b)) tensor I_k. Positivity follows without introducing a CP or Kraus premise. Zero ancillas, zero effects and unequal dimensions are included."))),
                DescribeRole.Theorem))));
}
