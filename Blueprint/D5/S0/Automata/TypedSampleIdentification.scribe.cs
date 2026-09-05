using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class TypedSampleIdentificationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Automata/TypedSampleIdentification.no_small_model_implies_state_lower_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite typed sample obstructions imply global DFAO state lower "
            + "bounds.",
        H("Typed Sparse-Sample Identification"),
        Blocks(Describe.Lean(
            DescribeId.Create("typed-finite-coloring-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("A finite coloring obstruction gives a global state lower bound"),
            StatementSource.FromAuthor(ObstructionFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A labeled sample carries exact words and outputs. A typed sample additionally assigns the legal partial-base state reached by every prefix.")),
                Paragraph(Text(
                    "Every fitting typed DFAO colors each sample prefix by the reached machine state. Equal colors automatically preserve terminal outputs, one-symbol transitions, and base-state types.")),
                Paragraph(Text(
                    "An injective relabeling sends a machine with at most k states into Fin k. Therefore the nonexistence of a Fin k coloring for any reindexed finite sample excludes every globally correct typed DFAO with at most k states."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Automata/DFAOStateLowerBound")),
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

    private static Formula ObstructionFormula() => Disp(Seq(
        Call("NoSmallModel", F.Id("k"), F.Id("S")),
        Sp, Land, Sp,
        Call("Fits", F.Id("M"), F.Id("S")),
        Sp, Implies, Sp,
        F.Id("k"), Sp, Lt, Sp, Call("card", F.Id("State")), Dot));
}
