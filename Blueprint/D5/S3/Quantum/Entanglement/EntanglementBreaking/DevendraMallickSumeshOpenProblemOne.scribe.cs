using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class DevendraMallickSumeshOpenProblemOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Decomposability of 2-entanglement-breaking maps"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.claim"),
                H("The universal decomposability assertion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Open Problem 1 of Devendra, Mallick and Sumesh, Mapping Cone of k-Entanglement Breaking Maps, asks whether every 2-entanglement-breaking complex-linear map between full complex matrix algebras is decomposable. The input and output dimensions are independently quantified and positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-devendramallicksumesh-openproblem1-counterexample"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_counterexample"),
                H("An indecomposable 2-entanglement-breaking map"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Taking k equal to two and both dimensions equal to 4194304 gives a 2-entanglement-breaking map that admits no decomposition into a completely positive and a completely copositive map."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-devendramallicksumeshopenproblemone-devendramallicksumesh-openproblem1-refuted"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/DevendraMallickSumeshOpenProblemOne.devendraMallickSumesh_openProblem1_refuted"),
                H("Refutation of universal decomposability"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The square counterexample belongs to the class quantified by the universal assertion and violates its conclusion."))),
                DescribeRole.Theorem))));
}
