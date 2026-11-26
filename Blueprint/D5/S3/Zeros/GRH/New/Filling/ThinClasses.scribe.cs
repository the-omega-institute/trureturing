using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class ThinClassesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thin Classes", H("Thin Classes"),
        Blocks(
            Paragraph(Text("Schur-test bound for total amplitude of a thin double-coset class of terms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/ThinClasses.tsum_amplitudeAbs_class_le"),
                H("tsum_amplitudeAbs_class_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let γ have level j, lie over (c, s, c') and satisfy ∏_v|𝗀(γ)|_v ≤ N^f·Filling.minorNorm j γ. Then the absolute amplitudes, for cut Bessel functions, over the double coset 𝖴⁰_c(g)γ𝖴⁰_c'(g) sum to at most ν·Filling.classSize j (𝗀*), 𝗀* = Filling.classGauge j c c' γ, ν = Filling.unipCovolume.")))))));
}
