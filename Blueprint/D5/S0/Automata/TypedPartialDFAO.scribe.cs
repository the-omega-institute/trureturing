using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class TypedPartialDFAODocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial output automata can be typed over a base automaton with exact "
            + "transition projection and leading-zero invariance.",
        H("Typed Partial DFAO"),
        Blocks(Describe.Lean(
            DescribeId.Create("successful-runs-project-to-the-base-automaton"),
            DeclarationHandle.Create(
                "D5/S0/Automata/TypedPartialDFAO.machine_run_type"),
            H("Successful runs project to the base automaton"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("map", F.Id("stateType"), Call("run", F.Id("w"))),
                Sp, Eq, Sp, Call("baseRun", F.Id("w")), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The base automaton marks representation-valid transitions, while the output machine may carry a finer state space.")),
                Paragraph(Text(
                    "An exact Option-map equation forces every defined machine transition to project to the prescribed base transition and forbids illegal transitions.")),
                Paragraph(Text(
                    "The run theorem lifts that local typing equation to arbitrary input words and keeps leading-zero invariance explicit."))),
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
