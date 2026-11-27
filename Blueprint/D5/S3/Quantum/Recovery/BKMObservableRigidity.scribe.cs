using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMObservableRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMObservableRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-observable BKM rigidity for the actual partial trace.",
        H("Fixed-observable BKM rigidity"), Blocks(
            Entry("weighted-lift-compression", "weightedLift_compression", "Physical modular compression",
                "Let A be positive definite on a finite retained space tensored with a nonempty "
                + "finite environment, and let S be its right partial trace. Weight each observable "
                + "on the right by the square root of its reference and vectorize column first. "
                + "The identity lift transported through these coordinates is an isometry. "
                + "It compresses the joint modular matrix exactly to the marginal modular matrix. "
                + "The two identities follow by testing against arbitrary weighted observables and "
                + "using the trace adjunction of the partial trace."),
            Entry("bkm-gap-rigidity", "bkmGap_rigidity", "Equality on a fixed Hermitian observable",
                "The marginal BKM form minus the joint BKM form on the identity lift is the "
                + "integral of the retained minus joint modular power forms. At each interior "
                + "exponent, this difference is a positive multiple of the integral of the joint "
                + "minus retained resolvent form against a positive weight. The isometry cancels "
                + "the common resolvent term and exact compression gives a nonnegative residual. "
                + "A zero BKM gap forces the half-power defect to vanish by continuity in the "
                + "exponent. Every positive-shift resolvent defect then vanishes by continuity in "
                + "the shift. Finite spectral separation gives intertwining for every real "
                + "function on the fixed weighted vector. Applying that intertwining to each "
                + "power gives the reverse implication."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
