using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class LocalLawGluingObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three pulled-back pair laws realize a four-class gluing-obstruction kernel.",
        H("Local-Law Gluing Obstruction Realization"),
        Blocks(
            Node("local-law-gluing-realization",
                "compatible_local_laws_can_lack_global_state_realization",
                "Gluing realization equivalence",
                Call("LegacyPrimitiveRealization", F.Id("localLawGluingArena"),
                    F.Id("LocalLawGluingStatement"), F.Id("localLawGluingRealization")),
                "The forward and backward maps translate set-image fibers and coded admission without invoking the frozen theorem."),
            Node("local-law-gluing-partition-count",
                "compatible_local_laws_can_lack_global_state_partition_count",
                "Four kernel classes", Seq(Call("card", F.Id("signatureClasses")),
                    Sp, Eq, Sp, D(4)),
                "Exhaustive evaluation of the three ADMIT bits yields four signatures."),
            Node("local-law-gluing-private-pair",
                "compatible_local_laws_can_lack_global_state_private_pair",
                "Private pair separation",
                Call("Not", Call("agrees", F.Id("localLawGluingRealization"),
                    F.Id("stateZero"), F.Id("stateOne"))),
                "The outer admission test separates 000 from 001."))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
