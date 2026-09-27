using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class BipartiteOverlapConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("U", F.Id("Type")), B("V", F.Id("Type")), B("I", F.Id("Type")),
             B("J", F.Id("Type")), B("d", Call("Boundary", F.Id("U"), F.Id("V"),
                 F.Id("I"), F.Id("J"))), .. extra], body);
    private static Formula L => Call("LeftPath", F.Id("d"));
    private static Formula R => Call("RightPath", F.Id("d"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rebracketing a legal alternating path preserves every half-edge and gives an invertible code.",
        H("Bipartite overlap conjugacy"),
        Blocks(
            Describe.Lean(DescribeId.Create("overlap-path-homeomorphism"),
                DeclarationHandle.Create(Prefix + "pathHomeomorph"),
                H("Construct the overlap homeomorphism"),
                StatementSource.FromAuthor(
                    Disp(All(
                        Call("Homeomorph", L, R),
                        B("topologyU", Call("TopologicalSpace", F.Id("U"))),
                        B("topologyV", Call("TopologicalSpace", F.Id("V")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The preceding and current half-edges give an explicit inverse in both directions. Coordinate evaluation proves continuity on the legal-path subspaces."))),
                DescribeRole.Definition))));
}
