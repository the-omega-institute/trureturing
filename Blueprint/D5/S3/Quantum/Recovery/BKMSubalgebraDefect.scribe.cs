using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMSubalgebraDefectDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMSubalgebraDefect.";

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
                + "include the result in the ambient algebra and apply the ambient BKM integral.",
                DescribeRole.Definition),
            Entry("transpose-action", "bkmTranspose_apply", "Resolvent formula for the transpose",
                "The first step in the transpose is computed by the actual resolvent "
                + "logarithmic derivative at the reduced base.",
                DescribeRole.Theorem),
            Entry("positive-transpose", "bkmTranspose_positive_commute", "Positive transpose projection test",
                "For a projection P that commutes with the reduced state, the reduced "
                + "BKM integral gives the positive compression of that state by P. The "
                + "transpose sends this test to the ambient BKM image of P. Projection "
                + "rigidity then forces the ambient state to commute with P.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string text,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
