using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class CompletionTowerMorphismDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/CompletionTowerMorphism.TowerMorphism.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural levelwise wormholes transport truth threads between completion towers.",
        H("Completion-Tower Morphisms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tower-morphism-transports-truth"),
                DeclarationHandle.Create(Prefix + "map_truth_thread"),
                H("Tower morphisms transport truth threads"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A tower morphism supplies one semiconjugate bridge at each level and "
                            + "requires the horizontal bridges to commute with the vertical "
                            + "completion bonds.")),
                    Paragraph(Text(
                        "Naturality transports coherence, while levelwise semiconjugacy transports "
                            + "fixedness. Their conjunction transports the full truth thread.")),
                    Paragraph(Text(
                        "Identity and composition are defined without asserting that every tower "
                            + "morphism is invertible."))),
                DescribeRole.Theorem))));

    private static Formula TransportFormula() => Disp(Seq(
        Call("IsTruthThread", F.Id("x")), Sp, Rightarrow, Sp,
        Call("IsTruthThread", Call("mapThread", F.Id("H"), F.Id("x")))));
}
