using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class RealConvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Convolution", H("Real Convolution"),
        Blocks(
            Paragraph(Text("Adelic unitary groups unimodular; quotient integral on definite groups equals weighted class sum. Right convolution at infinity: continuity, composition; discrete series kernels are cusp kernels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/RealConvolution.exists_form_eq_realConv"),
                H("exists_form_eq_realConv"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let e be a kernel on G_∞ (IsIdempotentKernel), K open in G_f, and F bounded, measurable, left Γ-invariant and right K-invariant. Then R(e)F is a form of type e fixed by K.")))))));
}
