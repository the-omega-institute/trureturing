using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSemantics;

internal sealed class SemanticOverreachLegacyBridgeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeSemantics/"
            + "SemanticOverreachLegacyBridge.semantic_overreach_iff_overreach";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic overreach is exactly its legacy propositional image.",
        H("Semantic Overreach Legacy Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-overreach-legacy-bridge"),
            DeclarationHandle.Create(Declaration),
            H("Semantic overreach descends exactly to legacy overreach"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The legacy predicate is the universe-polymorphic DECT 54.3 "
                        + "overreach criterion on the already frozen report, certificate, "
                        + "and propositional-semantics carriers.")),
                Paragraph(Text(
                    "Both directions preserve strict expansion, source scope, report, claim "
                        + "version, and exact report conditions. At the sole license "
                        + "existential, the proof invokes the frozen 57.3-C equivalence to "
                        + "convert typed certificate validity to and from its unique legacy "
                        + "image.")),
                Paragraph(Text(
                    "This discharges obligation 57.3-E from definition-escape-completion-theory "
                        + "atom generic-residual-6a153578be42b0dc05d1bf74fa4fe146f63b6fc6a6e6"
                        + "cee245ad9a9835653ca4."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula frame = F.Id("S");
        Formula report = F.Id("report");
        Formula oldDomain = F.Id("J");
        Formula semanticOverreach =
            Call("SemanticOverreach", frame, report, oldDomain);
        Formula legacyOverreach = Call(
            "Overreach",
            Seq(frame, Dot, F.Id("toLegacy")),
            report,
            oldDomain);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            frame, Comma, Sp,
            report, Comma, Sp,
            oldDomain, Comma, RowBreak, Grp(),
            semanticOverreach, Sp, Iff, RowBreak, Grp(),
            legacyOverreach, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
