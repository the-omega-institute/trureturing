using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class PrefixColoringSoundnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every DFAO compatible with a labeled prefix graph induces a "
            + "transition- and output-consistent state coloring.",
        H("Prefix Coloring Soundness"),
        Blocks(Describe.Lean(
            DescribeId.Create("uncolorability-excludes-compatible-machines"),
            DeclarationHandle.Create(
                "D5/S0/Automata/PrefixColoringSoundness.no_compatible_machine_of_no_coloring"),
            H("Uncolorability excludes compatible machines"),
            StatementSource.FromAuthor(Disp(Seq(
                Neg, Sp, Call("Nonempty", Call("Coloring", F.Id("G"), F.Id("S"))),
                Sp, Rightarrow, Sp,
                Neg, Sp, Exists, Sp, F.Id("M"), Colon, Sp,
                Call("Compatible", F.Id("M"), F.Id("G")), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each prefix node is colored by the machine state reached after reading its stored word.")),
                Paragraph(Text(
                    "Mathlib DFA append evaluation proves transition consistency, and compatibility with terminal labels proves output consistency.")),
                Paragraph(Text(
                    "Therefore an exact no-coloring certificate is a sound finite lower-bound certificate. The converse coloring-to-machine construction is intentionally deferred."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Automata/DFAOStateLowerBound")),
        ]));

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
}
