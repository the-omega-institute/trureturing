using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class PositiveCoarseRefinementRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary positive records of a general CP coarse map can fail complete positivity.",
        H("Positive refinement of a coarse qubit map"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-coarse-refinement-refutation"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveCoarseRefinementRefutation.result"),
                H("The transpose record is a counterexample"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The claim asserts that for all complex linear maps S,T on M_2(C), ordinary positivity of both maps, the trace identities Tr(S(X))=Tr(T(X))=Tr(X)/2 for every X, and complete positivity of S+T imply complete positivity of S. The theorem is the literal negation of that claim.")),
                    Paragraph(Text("Take S(X)=transpose(X)/2 and T(X)=(Tr(X) I-transpose(X))/2. Transposition preserves positivity. The second map is one half of conjugation by the real matrix with rows (0,1) and (-1,0), so it is positive as well. Both effects are I/2. Their sum is the completely depolarizing map X maps to Tr(X) I/2, with a four-matrix-unit Kraus representation.")),
                    Paragraph(Text("Applying the transpose branch tensored with the two-dimensional identity to the unnormalized Bell projector gives half the swap matrix. Its quadratic form on the antisymmetric vector is negative, contradicting positivity of that amplification. The example therefore concerns a general coarse CP map; it does not contradict scalar rigidity for positive refinements of a single canonical filter."))),
                DescribeRole.Theorem))));
}
