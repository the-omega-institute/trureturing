using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class ConnectedComponentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected Components", H("Connected Components"),
        Blocks(
            Paragraph(Text("Locally constant functions on tests are additive for idempotent partitions. Tilts of products of valuation rings; kernel of theta is (xi); untilting isomorphism. Cohomological equivalence can be checked on connected components, by Zorn's lemma.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/ConnectedComponents.isCohomEquiv_of_connected"),
                H("isCohomEquiv_of_connected"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let X, Y have continuous Λ-cohomology and U_a ⊂ Y (a ideals of R) be affine, behave like zero loci, and split densely along idempotents. If u: X → Y is an equivalence over U_a for each proper a containing e or 1 − e for every idempotent e, u is an equivalence.")))))));
}
