using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class LocalLawGluingObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-cycle gluing obstruction is expressed by three coded admission tests.",
        H("Local-Law Gluing Obstruction Arena"),
        Blocks(Describe.Lean(
            DescribeId.Create("local-law-gluing-arena"),
            DeclarationHandle.Create(Prefix + "localLawGluingArena"),
            H("Local-law gluing arena"),
            StatementSource.FromAuthor(Disp(Seq(F.Id("localLawGluingArena"),
                Colon, Sp, F.Id("PrimitiveLawArena"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The law compares existential fibers of the three realization ADMIT slots and rejects a jointly admitted triple."))),
            DescribeRole.Definition))));
}
