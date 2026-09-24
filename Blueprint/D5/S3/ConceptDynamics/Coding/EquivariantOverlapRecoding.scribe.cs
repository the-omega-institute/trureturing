using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class EquivariantOverlapRecodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding.";
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("U", F.Id("Type")), B("V", F.Id("Type")), B("I", F.Id("Type")),
             B("J", F.Id("Type")), B("H", F.Id("Type")), B("group", Call("Group", F.Id("H"))),
             B("d", Call("Boundary", F.Id("U"), F.Id("V"), F.Id("I"), F.Id("J"))),
             B("alpha", new Formula.TypeArrow(F.Id("U"), F.Id("H"))), .. extra], body);
    private static Formula L => Call("Prod", Call("LeftPath", F.Id("d")), F.Id("H"));
    private static Formula R => Call("Prod", Call("RightPath", F.Id("d")), F.Id("H"));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary transfer supplies an equivariant conjugacy of the two skew-product dynamics.",
        H("Equivariant overlap recoding"), Blocks(
            Describe.Lean(DescribeId.Create("skew-overlap-homeomorphism"),
                DeclarationHandle.Create(Prefix + "skewHomeomorph"),
                H("Construct the skew-product homeomorphism"),
                StatementSource.FromAuthor(Disp(All(Call("Homeomorph", L, R),
                    B("topologyU", Call("TopologicalSpace", F.Id("U"))),
                    B("topologyV", Call("TopologicalSpace", F.Id("V"))),
                    B("topologyH", Call("TopologicalSpace", F.Id("H"))),
                    B("continuousGroup", Call("IsTopologicalGroup", F.Id("H"))),
                    B("alphaContinuous", Call("Continuous", F.Id("alpha"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The path overlap code and the right group-coordinate transfer are constructed together. The inverse reads the preceding half-edge, and both directions are continuous."))),
                DescribeRole.Definition))));
}
