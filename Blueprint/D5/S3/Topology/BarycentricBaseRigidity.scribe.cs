using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BarycentricBaseRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximal-face criterion for contiguity at every depth",
        H("A maximal-face criterion for contiguity at every depth"),
        Blocks(Describe.Lean(
            DescribeId.Create("contiguity-fixes-original-vertices"),
            DeclarationHandle.Create(
                "D5/S3/Topology/BarycentricBaseRigidity.contiguity_chain_fixes_original_vertices"),
            H("Contiguity chains fix the original base vertices"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "For each original base vertex a, suppose a is the only vertex that can be adjoined to every maximal base face incident to a. " +
                "Then every contiguity chain starting at the inclusion fixes all original base vertices, at every common subdivision depth. " +
                "The distance bound first restricts the image of a maximal face barycenter using the fixed vertices of that face. " +
                "A second application restricts the next image of a to the faces that can be joined to that maximal face. " +
                "Intersecting those restrictions leaves only the iterated singleton at a."))),
            DescribeRole.Theorem))));
}
