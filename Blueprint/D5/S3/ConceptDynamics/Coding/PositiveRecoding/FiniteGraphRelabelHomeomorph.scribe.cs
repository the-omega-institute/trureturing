using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class FiniteGraphRelabelHomeomorphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relabel actual graph histories by vertex and edge equivalences.",
        H("Relabel actual graph histories by vertex and edge equivalences"),
        Blocks(
            Paragraph(Text("Relabel.symm reverses the given finite graph relabeling and proves its two endpoint laws. Relabel.homeomorph applies the edge equivalence coordinatewise to every legal integer-indexed history, uses the inverse equivalence for its inverse, and proves continuity in the product/subtype topology.")),
            Paragraph(Text("The construction ranges over V,E,W,D : Type* and graphs G,H; it assumes neither Fintype nor inhabitedness. The homeomorphism section assumes TopologicalSpace and DiscreteTopology on E and D. The filename does not strengthen those hypotheses into finiteness. Empty and infinite discrete carriers are not excluded by this API.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Lean(DescribeId.Create("positive-recoding-finitegraphrelabelhomeomorph-relabel-symm"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.symm"), H("Relabel.symm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Reverse the given vertex and edge equivalences and transport both endpoint laws. This constructs the inverse graph relabel on arbitrary carriers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-recoding-finitegraphrelabelhomeomorph-relabel-homeomorph"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.homeomorph"), H("Relabel.homeomorph"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Apply the edge equivalence at every integer coordinate. Its inverse and continuity follow coordinatewise under the stated discrete edge topologies."))), DescribeRole.Definition))));
}
