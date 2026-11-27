using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.MixedModel;

internal sealed class MixedModelIntegrableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Model Integrable", H("Mixed Model Integrable"),
        Blocks(
            Paragraph(Text("The mixed Schrödinger model function of a vector is continuous and integrable.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/MixedModel/MixedModelIntegrable.integrable_mixedTerm"),
                H("integrable_mixedTerm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a splitting of V over V₀ with p hyperbolic planes and f in 𝒮(V), the 𝒮(V₀)-valued function x ↦ f[x] of the mixed model is integrable on 𝔸^p.")))))));
}
