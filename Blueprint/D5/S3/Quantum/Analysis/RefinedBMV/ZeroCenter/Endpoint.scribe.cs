using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter;

internal sealed class RefinedBMVZeroCenterEndpointDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The singular four-spectrum refined BMV product bound",
        H("The singular four-spectrum refined BMV product bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-singular-four-spectrum-product"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint.product_bound_singular_all"),
                H("The product bound in every positive degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive integer p and every pair of complex positive semidefinite matrices A and B " +
                    "of the same finite size, assume A is singular and has at most four distinct eigenvalues, " +
                    "with arbitrary multiplicities. The mean trace of all words with p copies of A and three " +
                    "copies of B is at least the trace of the cube of A^(p/3) B, with A^(p/3) defined by spectral calculus. " +
                    "The repository proof addresses this spectral class of the product comparison discussed in " +
                    "Hägele's Section 7. At the zero center, scalar curvature bounds give a finite interval Gram " +
                    "decomposition. Each positive center has at most two distinct larger eigenvalues, where the " +
                    "ordered quartic and the corner inequality give a two-by-two positive semidefinite block. " +
                    "The cyclic trace-defect identity and the Schur product theorem give the matrix comparison."))),
                DescribeRole.Theorem))));
}
