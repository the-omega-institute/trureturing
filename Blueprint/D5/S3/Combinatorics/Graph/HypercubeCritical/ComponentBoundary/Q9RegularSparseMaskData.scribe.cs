using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9RegularSparseMaskDataDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9RegularSparseMaskData";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse masks for the regular order-ninety lift list",
        H("Sparse masks for the regular order-ninety lift list"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("regular-lift-records"),
                DeclarationHandle.Create(Module + ".records"),
                H("Thirty-two supports and their transverse masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input consists of thirty-two literal supports from the regular twelve-plus-three lift list. Each record stores its axis and three-direction mask."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("regular-list-exclusion"),
                DeclarationHandle.Create(Module + ".listed_support_not_universal"),
                H("Exclusion of every listed support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed local tests are evaluated by the Lean kernel. Every listed support fails universal weighted sharpness under any coherent switching."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-list-survival-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Survival of a listed candidate under universal weighted sharpness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim asks whether there exists a record in the literal list, a coherent switching of its support and a retained parity for which every real coordinate weighting admits a nonzero vector in the kernel of the signed boundary matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("regular-list-survival-refutation"),
                DeclarationHandle.Create(Module + ".result"),
                H("Refutation of survival in the regular lift list"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel-checked tests and their soundness exclude the proposed witness for any record, switching and retained parity. This settles the candidate-survival obligation for the thirty-two enumerated inputs. Exhaustion of the signed orbit census and the bridge from arbitrary components to this list remain separate obligations."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseMaskCertificate"))]));
}
