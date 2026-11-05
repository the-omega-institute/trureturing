using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalCoarseCellCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-cell coercivity for the original positive kernel", H("Finite-cell coercivity for the original positive kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-coarse-cell-coercivity"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalCoarseCellCoercivity.original_coarse_cell_coercivity"),
                H("An arbitrary positive coercivity constant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive window length D and positive beta, one finite strict uniform grid from zero to D works for every finite complex atomic family in the closed window with zero total mass. If the literal complex integral of the inclusive prefix vanishes on every coarse cell, beta times its whole-line squared L2 mass is at most the real part of the original quadratic form for P. Empty families, repeated locations, endpoint locations and zero energy are included.")),
                    Paragraph(Text("The full original P is exp(-abs(t)/2) times trivialT(abs(t)). ActualKernelMomentCertificate.pMultiplier uses every trivialCoeff(n) and actual rate 2*(n+1)+1/2; complete_positive_mixture_spectral_identity supplies the exact full-mixture energy. OriginalActualFourier.Ahat has kernel exp(-i*xi*u), and rho has density norm(Ahat)^2/(2*pi). The angular Plancherel theorem gives total rho mass equal to the actual prefix energy.")),
                    Paragraph(Text("Cell cancellation subtracts a constant phase from each cell and controls the resulting Fourier integral uniformly on a bounded frequency band. A finite uniform grid makes this band contain at most half the spatial energy. The actual positive-mixture nonnegativity controls the band, while the logarithmic multiplier lower bound controls its complement. The radius and grid are selected before the atom type and coefficients; the argument never divides by their energy.")),
                    Paragraph(Text("This is the finite atomic cell-integral consequence of the coarse-grid clause in AURIC Convergent Residual Certificates, Unitary Error Recursion, and Tolerant Robin Criterion. It does not identify cell-integral constraints with hat readouts, construct a completed detail space, realize an operator, or close the remaining operator and parent-transfer claims in that source atom."))),
                DescribeRole.Theorem))));
}
