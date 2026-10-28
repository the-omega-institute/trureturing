using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class CanonicalEntanglementFidelityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-root purification and one reference-first entanglement fidelity.",
        H("Canonical purification with the correct complex-state marginal"),
        Blocks(
            Describe.Lean(DescribeId.Create("fidelity"), DeclarationHandle.Create(Prefix + "fidelity"),
                H("Squared pure-reference fidelity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "In reference-first coordinates (r,i), let v(r,i) = (sqrt(rho))(i,r), where sqrt(rho) is the positive functional-calculus square root. "
                    + "Let P = |v><v|. For a genuine QuantumChannel C, apply C to each reference-indexed matrix block of P. "
                    + "The fidelity is Re <v|(id tensor C)(P)|v>. This is squared Uhlmann fidelity against a pure state, "
                    + "with no additional square, square root, or output normalization. The matrix argument is used on the positive trace-one domain certified below."))),
                DescribeRole.Definition),
            Entry("purification", "canonical_purification", "A density with input marginal rho",
                "For every finite complex positive semidefinite rho of trace one, P is positive semidefinite, has trace one, and tracing the reference factor gives rho. "
                + "The proof identifies that partial trace with sqrt(rho) sqrt(rho)-adjoint and uses positivity and positive-root square laws from pinned Mathlib. "
                + "The input index is the row of the square root; this orientation remains correct for non-real Hermitian states. "
                + "The eigenbasis purification supplied by the separately attributed physlib port FiniteDensityPurification is not silently identified with this root vector."),
            Entry("flip", "overlap_factor_flip", "Exact tensor-factor relabeling",
                "For every vector v and matrix T, swapping both factors in v and both row and column factors in T leaves the complex overlap unchanged. "
                + "Two finite-sum changes of variables prove the equality. The Burri comparison consumes this lemma to connect the channel-first reverse calculation to the common reference-first quantity."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
