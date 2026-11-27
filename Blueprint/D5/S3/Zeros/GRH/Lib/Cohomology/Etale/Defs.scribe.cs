using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Defs", H("Defs"),
        Blocks(
            Paragraph(Text("Cohomology as Ext of presheaves: equivalences, dense subfunctors, comparisons, fibre powers, additivity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Defs.isoOfAppBijective"),
                H("isoOfAppBijective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A natural transformation γ: F → G that is bijective on every object, as an isomorphism F ≅ G; the target is a concrete category whose forgetful functor reflects isomorphisms.")))))));
}
