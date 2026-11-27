using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class GramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram", H("Gram"),
        Blocks(
            Paragraph(Text("Contravariant form on Weyl's lattice: symmetric, positive, invariant, inverse to the Fischer product up to the hook number.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Gram.range_toPoly"),
                H("range_toPoly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over ℂ, the map ξ ↦ Σ_i (Gξ)_i b_i, with G the Gram matrix and b_i the basis minor products, has image exactly the module nablaFam of Borel semi-invariant polynomials of the weight given by κ.")))))));
}
