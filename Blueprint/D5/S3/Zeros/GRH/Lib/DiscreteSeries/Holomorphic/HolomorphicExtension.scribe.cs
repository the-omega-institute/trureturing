using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic;

internal sealed class HolomorphicExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic Extension", H("Holomorphic Extension"),
        Blocks(
            Paragraph(Text("Coefficients of highest vectors extend holomorphically to G·B; mean value over circle.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicExtension.circle_mean_weightMinors"),
                H("circle_mean_weightMinors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Circle mean: let ε' be 1 or ε, o injective, u_τ dominant and g_τ block diagonal for ε', F satisfy IsHolOfWeight for u, ε', q analytic on the closed disc. The mean over |s| = 1 of F(diag(s^o)g) ∏ s^{−o_i u_{τ,i}} q(s) is q(0) ∏_τ m_{u_τ}(g_τ) F(1).")))))));
}
