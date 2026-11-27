using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class DefiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Definite", H("Definite"),
        Blocks(
            Paragraph(Text("Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms (known result; see Lib.Adelic.CuspForms.Petersson).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/Definite.exists_height_le_mul"),
                H("exists_height_le_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For compact K ⊆ G there is C ≥ 1 with ht(k) ≤ C·ht(g) whenever g⁻¹γk ∈ K for some γ ∈ Γ.")))))));
}
