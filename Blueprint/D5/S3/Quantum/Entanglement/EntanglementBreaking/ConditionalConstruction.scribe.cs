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
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a traceless Hermitian direction at dimension d, impose the Schmidt-cutoff quadratic bound and the lower energy bound. Positivity of the test and its output partial transpose then yields a k-entanglement-breaking indecomposable map with the stated input-first Choi matrix."))),
                DescribeRole.Theorem))));
}
