using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class SomerUniformSubsequenceCertificateRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/SomerUniformSubsequenceCertificateRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete finite counterexample is retained by six independently sensitive CUT readouts.",
        H("SomerUniformSubsequenceCertificateRegistration"),
        Blocks(
            Node("certificateArena", "The certificate law requires equality with the actual "
                + "six-code word and every field of its CounterexampleCertificate."),
            Node("certificateRealization", "Each CUT slot returns the actual certificate word's "
                + "code at that position."),
            Node("bumpCode", "Cyclic increment modulo five supplies a different code at any "
                + "chosen position."),
            Node("alteredRealization", "The selected slot uses bumpCode while the other five "
                + "slots preserve the actual word, witnessing independent sensitivity."))));

    private static DocumentBlock.Describe Node(string declaration, string text) =>
        Describe.Lean(
            DescribeId.Create("somer-registration-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
