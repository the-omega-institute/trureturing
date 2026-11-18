using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMSubalgebraDefectDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMSubalgebraDefect.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/hiaikosakipetzruskai2013monotonemetrics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity of the BKM transpose forces commutation with projections in the "
        + "reduced state's commutant inside the star-subalgebra.",
        H("Projection tests for the BKM transpose"),
        Blocks(
            Entry("trace-expectation", "traceExpectation", "The tracial expectation",
                "Restrict the codomain of the native ordered GNS projection at the "
                + "normalized identity to the given unital star-subalgebra.",
                DescribeRole.Definition),
            Entry("bkm-transpose", "bkmTranspose", "The actual BKM transpose",
                "Invert the restricted BKM integral at the reduced faithful base, then "
                + "include the result in the ambient algebra and apply the ambient BKM integral. "
                + "The order of composition follows the metric transpose in Appendix B of "
                + "Hiai, Kosaki, Petz, and Ruskai.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Entry("positive-transpose", "bkmTranspose_positive_commute", "Positive transpose projection test",
                "For a projection P that commutes with the reduced state, the reduced "
                + "BKM integral gives the positive compression of that state by P. The "
                + "transpose sends this test to the ambient BKM image of P. Projection "
                + "rigidity then forces the ambient state to commute with P.",
                DescribeRole.Theorem),
            Entry("positivity-defect", "positivityDefect", "Defect of the BKM transpose",
                "Take the supremum of negative spectral mass over the images of positive "
                + "elements of the subalgebra with ambient trace one.",
                DescribeRole.Definition),
            Entry("pinching-trace-norm", "bkm_pinching_traceNorm_le", "Trace-norm error of pinching",
                "Test the transpose on the reduced state times each projection. The exact "
                + "inverse identifies the output with the ambient BKM image, so its negative "
                + "mass controls the squared Frobenius norm of the corresponding off-diagonal "
                + "row. Row orthogonality allows their squared norms to be summed. The finite "
                + "Schatten bound gives the trace-norm error with the coefficient stated in "
                + "the theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text,
        DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
