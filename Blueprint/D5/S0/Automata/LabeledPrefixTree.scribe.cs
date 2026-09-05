using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class LabeledPrefixTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite labeled samples carry a canonical finite family of "
            + "prefix occurrences with exact leaf and extension semantics.",
        H("Labeled Prefix Occurrences"),
        Blocks(Describe.Lean(
            DescribeId.Create("prefix-sample-leaf-word"),
            DeclarationHandle.Create(
                "D5/S0/Automata/LabeledPrefixTree.prefixSample_leaf_word"),
            H("Finite-sample leaves recover the registered sparse inputs"),
            StatementSource.FromAuthor(LeafWordFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A prefix occurrence records a sample index and a legal cut position. The leaf occurrence is the full word, and the theorem identifies it exactly with the corresponding sparse-problem input.")),
                Paragraph(Text(
                    "Equal prefix words may have multiple occurrences. Their later identification is carried by proofs rather than silently quotienting the finite carrier."))),
            DescribeRole.Theorem)),
        []));

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

    private static Formula LeafWordFormula() => Disp(Seq(
        Call("prefixWord",
            Call("prefixSample", F.Id("P"), F.Id("N")),
            Call("leaf", F.Id("i"))),
        Sp, Eq, Sp,
        Call("input", F.Id("P"), F.Id("i"))));
}
