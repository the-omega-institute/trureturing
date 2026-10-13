using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMContractionSymmetryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMContractionSymmetry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact local EJM contraction symmetry for tail representatives.",
        H("Tail contractions inherit the earned centered-score symmetries"),
        Blocks(
            Paragraph(Text("Fixing any head event and cancelling the common leading coefficient term in the already proved centered-score symmetry yields the exact contraction symmetry. The proof retains the full head sum. A finite replay may calculate one representative contraction per tail orbit, then transport it by these earned identities; representative arithmetic and every concrete tail match remain separate obligations.")),
            Describe.Lean(DescribeId.Create("triangle-coordinate"),
                DeclarationHandle.Create(Prefix + "triangleContraction_coordinate"),
                H("Triangle-tail coordinate action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact three-head contraction is invariant under each induced seven-tail coordinate action when F has the corresponding full local coordinate symmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-coordinate"),
                DeclarationHandle.Create(Prefix + "singletonContraction_coordinate"),
                H("Singleton-tail coordinate action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four singleton-head terms are invariant under the induced eight-tail coordinate action when F has the corresponding full local coordinate symmetry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("triangle-relabel"),
                DeclarationHandle.Create(Prefix + "triangleContraction_relabel"),
                H("Triangle-tail outcome bijection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common outcome bijection preserving F preserves the entire weighted triangle-head contraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("singleton-relabel"),
                DeclarationHandle.Create(Prefix + "singletonContraction_relabel"),
                H("Singleton-tail outcome bijection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common outcome bijection preserving F preserves the exact singleton-head contraction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-triangle-coordinate"),
                DeclarationHandle.Create(Prefix + "actual_triangleContraction_coordinate"),
                H("Actual F1 tail-coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual coefficient lookup supplies the earned symmetry needed to reuse contracted seven-tail representatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-singleton-coordinate"),
                DeclarationHandle.Create(Prefix + "actual_singletonContraction_coordinate"),
                H("Actual F2 tail-coordinate symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual coefficient lookup supplies the earned symmetry needed to reuse contracted eight-tail representatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-triangle-relabel"),
                DeclarationHandle.Create(Prefix + "actual_triangleContraction_relabel"),
                H("Actual F1 tail-outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original F1 contraction is invariant under all common outcome bijections, allowing equality-pattern tail representatives."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-singleton-relabel"),
                DeclarationHandle.Create(Prefix + "actual_singletonContraction_relabel"),
                H("Actual F2 tail-outcome symmetry"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original F2 contraction is invariant under all common outcome bijections. The singleton contraction contains four F2 terms; its factor 64 remains in the separate centered score."))), DescribeRole.Theorem))));
}
