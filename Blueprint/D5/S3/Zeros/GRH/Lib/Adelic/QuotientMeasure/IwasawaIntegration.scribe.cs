using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure;

internal sealed class IwasawaIntegrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iwasawa Integration", H("Iwasawa Integration"),
        Blocks(
            Paragraph(Text("Iwasawa integration formula; quotient integral of N-invariant functions in coordinates n m k.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/IwasawaIntegration.integral_orbitMeasure_iwasawa"),
                H("integral_orbitMeasure_iwasawa"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In Iwasawa coordinates G = N i(M) K, let Γ be discrete, contain all i(δ_d), lie in ⋃N·i(δ_d)⁻¹, with Γ∩N cocompact in N. For F invariant under N, Γ: ∫F over the quotient is c∫w(m)F(i(m)k), if convergent, m over a measure unfolding ν along δ; c ≠ 0.")))))));
}
