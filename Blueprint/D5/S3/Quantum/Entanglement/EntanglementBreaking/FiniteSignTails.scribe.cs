using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class FiniteSignTailsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Concentration for a finite Hermitian sign matrix"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-finitesigntails-signcubemeasure"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeMeasure"),
                H("Uniform measure on the sign cube"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The probability space is the set of all Boolean assignments to the sign coordinates, with uniform measure."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-finitesigntails-signcubesample-quadratic-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/FiniteSignTails.signCubeSample_quadratic_tail"),
                H("Fixed-vector quadratic tail"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A quadratic form at a vector of Euclidean norm at most one is a real linear form in independent signed variables. Its squared coefficient norm is bounded by 18/25. The two one-sided sub-Gaussian bounds give the absolute tail."))),
                DescribeRole.Theorem))));
}
