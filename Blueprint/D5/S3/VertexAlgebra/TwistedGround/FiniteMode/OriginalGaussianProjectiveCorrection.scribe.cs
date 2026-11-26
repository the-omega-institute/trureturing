using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FiniteMode;

internal sealed class OriginalGaussianProjectiveCorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical Gaussian correction is determined by the actual native period-ratio derivative quotient.",
        H("Canonical Gaussian period correction and the native quotient"),
        Blocks(Describe.Lean(DescribeId.Create("original-correction-projective"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection.original_correction_projective"),
            H("The exact correction bridge in both directions"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/nist2010schwarzian")),
            Blocks(
                Paragraph(Text("For every complex r in the full open lens, use exactly "
                    + "OriginalGaussianFiniteCandidateModes.ell=P'/P and its canonical k=r(1-r)ell. "
                    + "For the literal tau=iP(1-r)/P(r), g is the actual derivative quotient "
                    + "deriv(deriv tau)/deriv tau. Then g=-(1-2r+2k)/(r(1-r)), and "
                    + "k=(2r-1)/2-r(1-r)g/2, with no additional premises.")),
                Paragraph(Text("The proof consumes the native period theorem's actual quotient "
                    + "inference and the canonical definitions of ell and k. It solves the resulting "
                    + "identity using the nonzero lens factors. The correction is thus attached "
                    + "to the existing Gaussian object, rather than a replacement period or "
                    + "an assumed projective connection. No all-mode kernel, operator transport, "
                    + "stress tensor, anomaly or physical spacetime conclusion is included."))),
            DescribeRole.Theorem))));
}
