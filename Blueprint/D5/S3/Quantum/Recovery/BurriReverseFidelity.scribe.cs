using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReverseFidelityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReverseFidelity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entanglement fidelity of the actual reverse-instance composite channels.",
        H("The physical channel with its identity reference"),
        Blocks(
            Entry("reference", "canonical_reference_purification", "The canonical reference density",
                "The maximally entangled vector is exactly the vectorized positive square root of rho = I/2. Its rank-one density is positive, has trace one, and has the required reference marginal."),
            Entry("tensor", "tensor_reference_kraus", "The actual tensor extension",
                "The channel acts on the first factor, and the reference is the second. Applying the actual channel to each reference-indexed matrix block is exactly the Kraus action by K tensor I. Thus the purified overlap is the squared-fidelity convention for a pure canonical reference."),
            Entry("actual", "actual_recovered_purification", "The actual recovered purification",
                "Composing the actual decoder channel with the actual physical noise channel and adjoining the identity reference gives exactly the previously calculated recovered purification, retaining all pairs of environment labels."),
            Entry("strict", "actual_strict_fidelity", "The strict reverse comparison",
                "For this fixed explicit instance, the source-row composite has strictly smaller entanglement fidelity than the ordinary reference-completed Petz composite. The Petz value is 27/31. The strictness follows from the exact radical sum-of-squares gap. This is a single reverse instance; no joint theorem about both directions is asserted."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
