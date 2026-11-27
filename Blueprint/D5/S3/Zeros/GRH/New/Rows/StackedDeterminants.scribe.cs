using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class StackedDeterminantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stacked Determinants", H("Stacked Determinants"),
        Blocks(
            Paragraph(Text("Record of auxiliary dual pair: levels, characters, data, theta descent, Hecke test polynomial. Record of the splitting of V, residue rings modulo squared level, generator idele. Bordered determinant, trivial modulus, the carrier lift and the summing form. Products of bordered determinants, their substitution law, and coordinates in a Schur basis.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/StackedDeterminants.twoSidedSubst_stackedDetProd"),
                H("twoSidedSubst_stackedDetProd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The substitution x_τ ↦ c_τᵀ x_τ g_τᵀ sends the product over τ, k of the determinants of M_{τk} g_τᵀ stacked over x_τ to ∏_τ (det c_τ · det g_τ)^{#ι(τ)} times the same product for the matrices M_{τk}.")))))));
}
