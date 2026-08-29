using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class SemanticTransportCertificateValidityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "SemanticTransportCertificateValidity."
            + "valid_semantic_transport_cert_iff_valid_transport_cert";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed transport-certificate validity is exactly its legacy propositional image.",
        H("Semantic Transport-Certificate Validity"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-transport-certificate-validity"),
            DeclarationHandle.Create(Declaration),
            H("Typed and legacy transport-certificate validity are equivalent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The typed certificate names strict expansion, a claim-bound source "
                        + "receipt, conditional transport, total prediction coverage on the "
                        + "new-only domain, and a result-bearing refuting failure.")),
                Paragraph(Text(
                    "The forward implication forgets only the stored run result. In the "
                        + "reverse implication, failure and refutation initially expose two "
                        + "existential results; both are outputs of the same partial run at "
                        + "the same point, so injectivity of Option.some identifies them "
                        + "without decidable equality or a result-uniqueness axiom.")),
                Paragraph(Text(
                    "This discharges obligation 57.3-C from definition-escape-completion-theory "
                        + "atom generic-residual-52c9a2ebbc45db7def84de526f0e46314b1acd696edde"
                        + "2615911dddda21aa70f."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula frame = F.Id("S");
        Formula certificate = F.Id("cert");
        Formula claim = F.Id("claim");
        Formula oldDomain = F.Id("J");
        Formula newDomain = Seq(F.Id("J"), Apos);
        Formula version = F.Id("version");
        Formula legacyFrame = Seq(frame, Dot, F.Id("toLegacy"));
        Formula typedValidity = Call(
            "ValidSemanticTransportCert",
            frame,
            certificate,
            claim,
            oldDomain,
            newDomain,
            version);
        Formula legacyValidity = Call(
            "ValidTransportCert",
            legacyFrame,
            certificate,
            claim,
            oldDomain,
            newDomain,
            version);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            frame, Comma, Sp,
            certificate, Comma, Sp,
            claim, Comma, Sp,
            oldDomain, Comma, Sp,
            newDomain, Comma, Sp,
            version, Comma, RowBreak, Grp(),
            typedValidity, Sp, Iff, RowBreak, Grp(),
            legacyValidity, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
