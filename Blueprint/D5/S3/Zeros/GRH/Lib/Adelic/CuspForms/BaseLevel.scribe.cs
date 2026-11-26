using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class BaseLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Level", H("Base Level"),
        Blocks(
            Paragraph(Text("Isotypic spaces of Hecke eigenvalues at almost all places: independence, attached Galois representation. Records for auxiliary Taylor-Wiles places, base level, integral lattices and eigensystems of forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/BaseLevel.exists_isotypic_of_isSphericalOff"),
                H("exists_isotypic_of_isSphericalOff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A nonzero form of maximal level off S that is a spherical Hecke eigenform at every split w with w, w̄ not in S lies in some isotypic space.")))))));
}
