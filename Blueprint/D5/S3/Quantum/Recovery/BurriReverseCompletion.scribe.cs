using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BurriReverseCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Recovery/BurriReverseCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full source SVD and its physically irrelevant null-space freedom.",
        H("The actual source construction"),
        Blocks(
            Entry("svd", "full_source_svd", "A full nonnegative SVD",
                "The active nonnegative SVD extends to the full source matrix by padding both unitary factors with the identity and all inactive singular values with zero. The source-ordered adjoint product of the two factors is precisely the specified sourceU."),
            Entry("purification", "source_purification_identity", "The source purification identity",
                "The fixed ancillary vector is normalized and W is the actual permutation unitary. Applying W to the physical output with this ancilla gives the full canonical square-root purification of the actual complementary state, as in Appendix A.9."),
            Entry("amplitude", "source_recovered_amplitude", "The recovered amplitude convention",
                "The actual source-row recovery multiplies the canonical amplitude on its right by the transpose of sourceU. The positive right-polar product is M sourceU, with M defined by the transposed product of the two positive roots; these two occurrences of a transpose have distinct roles."),
            Entry("completion", "source_decoder_completion_independent", "Every allowed completion has the same decoder rows",
                "For any complex coisometry Uprime with M Uprime positive semidefinite, uniqueness of the positive square root first determines M Uprime. Invertibility of the active matrix then determines the action on J. Consequently all Appendix A.11 Kraus rows after the actual ancilla preparation agree with the specified decoder, for every physical input and every environment label. No off-support equality is required."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
