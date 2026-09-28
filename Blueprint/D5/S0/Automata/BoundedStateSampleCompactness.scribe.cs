using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class BoundedStateSampleCompactnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite samples characterize bounded-state output automata.",
        H("Bounded State Sample Compactness"),
        Blocks(Describe.Lean(
            DescribeId.Create("bounded-state-sample-compactness"),
            DeclarationHandle.Create(
                "D5/S0/Automata/BoundedStateSampleCompactness.bounded_state_sample_compactness"),
            H("Finite obstructions for a fixed state budget"),
            StatementSource.FromAuthor(Disp(Seq(
                Call("Realizable", F.Id("s"), F.Id("D"), F.Id("f")),
                Sp, Iff, Sp, Forall, Sp, F.Id("E"), Sp, Subseteq, Sp, F.Id("D"),
                Comma, Sp, Call("Finite", F.Id("E")), Sp, Rightarrow, Sp,
                Call("Realizable", F.Id("s"), F.Id("E"), F.Id("f")), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let A and Y be finite alphabets, D any set of words over A, f a function from D to Y, and s a natural number. Realizable(s,E,f) means that some finite state type Q with cardinality at most s supports a total deterministic output automaton whose output on every word in E equals f at that word. State types and alphabets may lie in arbitrary universes. No labels are imposed outside D.")),
                Paragraph(Text(
                    "Global correctness restricts to every finite sample. Conversely, embed each state type of size at most s into Fin s, extend the transitions through a retraction, and read the original outputs through that retraction. Induction on words shows that all reached states and outputs are preserved.")),
                Paragraph(Text(
                    "A candidate on Fin s is determined by its initial state, transition table, and output table; the acceptance set is irrelevant to output evaluation. These tables form a finite product. If every candidate fails on D, choose one failing word for each table. Their finite image excludes every candidate, contradicting realizability of every finite sample.")),
                Paragraph(Math(In(Seq(Call("card", F.Id("Tables")), Sp, Eq, Sp,
                    F.Id("s"), Sp, F.Id("s"), Caret, Grp(Seq(F.Id("s"), Sp,
                        Call("card", F.Id("A")))), Sp,
                    Call("card", F.Id("Y")), Caret, Grp(F.Id("s")), Dot)))),
                Paragraph(Text(
                    "Consequently, global nonexistence has a finite sample obstruction. A sound unsatisfiability certificate for exact sample labels therefore excludes a global machine with the same state budget. Satisfiability of one sample gives no such global conclusion. The argument supplies no effective bound on the lengths of the failing words.")),
                Paragraph(Text(
                    "The equivalence includes empty domains, empty output alphabets, and zero state budgets. In particular it applies when Y is nonempty and s is positive. Every sample family includes the empty sample; an automaton must still have an initial state and an output map."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S0/Automata/FiniteSampleRestriction"))]));

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
