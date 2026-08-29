using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class WormholeCategoryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Bridges/WormholeCategory.Wormhole.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed semiconjugate bridges compose and transport fixed behavior.",
        H("Wormhole Category"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wormholes-compose-associatively"),
                DeclarationHandle.Create(Prefix + "compose_assoc"),
                H("Typed wormholes compose associatively"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A dynamical world consists of a typed state carrier and one update. "
                            + "A wormhole is a map that semiconjugates the source update to the "
                            + "target update.")),
                    Paragraph(Text(
                        "Identity and composition preserve the semiconjugacy equation. "
                            + "The resulting bridge calculus is associative and transports "
                            + "fixed points and finite iterates.")),
                    Paragraph(Text(
                        "No inverse, carrier identification, or higher-jet preservation is "
                            + "assumed."))),
                DescribeRole.Theorem))));

    private static Formula CompositionFormula() => Disp(Seq(
        Call("compose", F.Id("h3"), Call("compose", F.Id("h2"), F.Id("h1"))),
        Sp, Eq, Sp,
        Call("compose", Call("compose", F.Id("h3"), F.Id("h2")), F.Id("h1"))));
}
