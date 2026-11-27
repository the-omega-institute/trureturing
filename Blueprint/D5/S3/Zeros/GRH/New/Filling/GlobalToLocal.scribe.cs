using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class GlobalToLocalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Global To Local", H("Global To Local"),
        Blocks(
            Paragraph(Text("Dictionary between global data and the places in T; phase sums as local integrals.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/GlobalToLocal.correlation_smul_eq_cosetAmplitude"),
                H("correlation_smul_eq_cosetAmplitude"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Unfolding: let σ fix all e_a, e*_a, γ = w_pσ, h_c⁻¹γh_c' and 1/g be integral off T, k ∈ K, k_T⁻¹ab⁻¹ ∈ K(g). Then entry (a,b) of Level.correlation at (h_c⁻¹σh_c')_T⁻¹, times the archimedean besselCorrelation at γ, equals κ_ϱ(p,1)·M(K(g))·Filling.cosetAmplitude over (c, k̄, c'), cut off at T.")))))));
}
