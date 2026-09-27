using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class SingularRightGridDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singular right-grid sum approximates its integral uniformly with a square-root mesh error.",
        H("Singular Quadrature for Complex Sobolev Representatives"),
        Blocks(Describe.Lean(
            DescribeId.Create("uniform-singular-right-grid"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/SingularRightGrid.result"),
            H("A uniform estimate including both endpoints"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A be positive and let f be a complex-valued absolutely continuous "
                    + "function on the closed interval from zero to A, with square-integrable "
                    + "actual derivative. Set g(v) equal to the squared norm of f(v) minus the "
                    + "squared norm of f(0). For every positive mesh h and endpoint b satisfying "
                    + "h <= b <= A, compare the sum of g(kh)/k for k from one through floor(b/h) "
                    + "with the integral of g(v)/v from zero to b. The absolute error is bounded "
                    + "by 14 times (1/sqrt(A) + sqrt(A)), times sqrt(h), times the integral of "
                    + "the squared norm of f plus the squared norm of its derivative.")),
                Paragraph(Text(
                    "The constant depends only on A. In particular it works simultaneously "
                    + "for every b in any fixed interval [A0,A] whenever 0 < h <= A0. "
                    + "The proof includes the singular first cell and the final partial cell "
                    + "created by the floor. Absolute continuity, rather than continuous "
                    + "differentiability, is the regularity assumption.")),
                Paragraph(Text(
                    "For a real absolutely continuous function vanishing at zero, the proof "
                    + "first obtains the error bound 7 sqrt(h) times the L2 norm of its "
                    + "derivative. The remaining full cells are controlled by the integrable "
                    + "derivative of g(v)/v away from zero. The Sobolev energy controls the "
                    + "derivative of the squared norm. This is a deterministic quadrature "
                    + "estimate; harmonic counterterms and stochastic spectral convergence "
                    + "are separate conclusions."))),
            DescribeRole.Theorem))));
}
