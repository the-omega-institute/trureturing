using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class ConditionalConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian matrix and a PPT test give an indecomposable k-entanglement-breaking map.",
        H("Conditional construction of an indecomposable map"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-conditionalconstruction-conditional-indecomposable-keb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/ConditionalConstruction.conditional_indecomposable_kEB"),
                H("Schmidt bound and positive partial transpose suffice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let 1 ≤ k ≤ d and let H be a traceless Hermitian direction satisfying the Schmidt-cutoff quadratic bound and the lower energy bound. If the test and its output partial transpose are positive semidefinite, the map with input-first Choi matrix I − (16/d)H is k-entanglement-breaking and indecomposable."))),
                DescribeRole.Theorem))));
}
