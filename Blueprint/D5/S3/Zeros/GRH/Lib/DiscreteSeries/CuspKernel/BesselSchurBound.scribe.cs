using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.CuspKernel;

internal sealed class BesselSchurBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Schur Bound", H("Bessel Schur Bound"),
        Blocks(
            Paragraph(Text("Definitions: convolution, Bessel functions, unitary action of U(κ). Schur orthogonality: convolution with reproduced functions is an isometry up to the degree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/BesselSchurBound.lintegral_sq_convolve_convolve_le"),
                H("lintegral_sq_convolve_convolve_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Under the hypotheses of IsBoundedMeasurable.lintegral_sq_convolve, for integrable φ the function y ↦ ∫φ(a)(F*x)(ya)da has squared L²(ν) norm at most (‖x‖₂²/d)·(‖F‖²_ν/d)·‖φ‖₂².")))))));
}
