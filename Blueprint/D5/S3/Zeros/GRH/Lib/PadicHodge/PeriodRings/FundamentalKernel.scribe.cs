using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicHodge.PeriodRings;

internal sealed class FundamentalKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fundamental Kernel", H("Fundamental Kernel"),
        Blocks(
            Paragraph(Text("Kernel of the fundamental exact sequence for B_max; pole bound by powers of μ.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicHodge/PeriodRings/FundamentalKernel.exists_padic_eq_of_frobEnd_fixed"),
                H("exists_padic_eq_of_frobEnd_fixed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Kernel in the fundamental exact sequence: an element y of B with φ(y) = y whose image in B_dR lies in B_dR^+ belongs to Q_p.")))))));
}
