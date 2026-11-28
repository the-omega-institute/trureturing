using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class ReproducingKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reproducing Kernel", H("Reproducing Kernel"),
        Blocks(
            Paragraph(Text("Forms reproduced by a cusp kernel decay rapidly; finite dimension at fixed level. A bounded Poincaré series projected term by term is a form of given level. Poincaré series of the idempotent kernel is a form of level K.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel.exists_kernel_form"),
                H("exists_kernel_form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Poincaré series: for a cusp kernel e, x ∈ G and a level K (IsLevel), there is a K-fixed form k of type e on V with conj k(g) = ∑_{γ∈Γ} e((xγg)_∞)·1_K((xγg)_f) for all g ∈ G.")))))));
}
