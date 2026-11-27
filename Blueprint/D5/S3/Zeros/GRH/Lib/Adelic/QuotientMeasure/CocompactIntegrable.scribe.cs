using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure;

internal sealed class CocompactIntegrableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cocompact Integrable", H("Cocompact Integrable"),
        Blocks(
            Paragraph(Text("Unfolding quotient integrals in stages; pushing quotient measures along surjections. Unfolding a sum over an orbit or block to the stabiliser quotient. Quotient integral vanishes when averaging eigenvalue differs from modulus, or nontrivial phase. Continuous invariant functions for cocompact subgroups are integrable; cocompactness of products.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/CocompactIntegrable.integral_quotMeasure_eq_zero_of_twist"),
                H("integral_quotMeasure_eq_zero_of_twist"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Γ be a discrete subgroup of G, μ left invariant, F continuous and left Γ-invariant. If F(uy) = cF(y) for all y, for some u in G and c with |c| = 1, c ≠ 1, then ∫_{Γ\\G} F dμ = 0.")))))));
}
