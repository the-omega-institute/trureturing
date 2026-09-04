using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class ArenaDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/Arena.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite arenas keep construction separate from the seal's nondegeneracy check.",
        H("Finite Information-Escape Arenas"),
        Blocks(
            DefinitionNode("finite-arena", "Arena", "Finite arena",
                "An arena packages a state type, its finite enumeration, and decidable equality."),
            DefinitionNode("arena-cardinality", "Arena.card", "Arena cardinality",
                "The arena cardinality is computed from its stored finite enumeration."),
            DefinitionNode("arena-nondegeneracy", "Arena.Nondegenerate", "Arena nondegeneracy",
                "Nondegeneracy is the separately decidable requirement that the state cardinality is at least two."),
            DefinitionNode("arena-from-fintype", "Arena.ofFintype", "Arena from a finite type",
                "Any type with finite enumeration and decidable equality can be packaged as an arena."),
            Describe.Lean(
                DescribeId.Create("nondegenerate-arena-has-distinct-states"),
                DeclarationHandle.Create(Prefix + "Arena.exists_ne_of_nondegenerate"),
                H("A nondegenerate arena has distinct states"),
                StatementSource.FromAuthor(DistinctStatesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cardinal lower bound converts to the standard finite-type distinct-pair witness."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DistinctStatesFormula()
    {
        Formula arena = F.Id("arena");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Disp(Seq(
            Call("Nondegenerate", arena), Sp, Rightarrow, Sp,
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, Call("State", arena), Comma, Sp,
            x, Sp, Neq, Sp, y, Dot));
    }
}
