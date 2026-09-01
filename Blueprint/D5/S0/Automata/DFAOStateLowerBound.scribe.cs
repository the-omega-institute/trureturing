using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class DFAOStateLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration = "D5/S0/Automata/DFAOStateLowerBound.state_lower_bound_of_distinguishing_family";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite distinguishing continuations certify state lower bounds for "
            + "output automata built on Mathlib DFA.",
        H("DFAO State Lower Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("dfao-state-lower-bound"),
            DeclarationHandle.Create(Declaration),
            H("Distinguishing continuations force distinct reached states"),
            StatementSource.FromAuthor(LowerBoundFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A DFAO reuses Mathlib's deterministic finite automaton as its transition carrier and adds one output map on states. Correctness may be restricted to an explicitly declared sparse language.")),
                Paragraph(Text(
                    "A finite certificate chooses prefixes and a legal pair-specific continuation for every two distinct indices. The target outputs after that common continuation must differ.")),
                Paragraph(Text(
                    "If two certified prefixes reached the same machine state, the upstream append evaluation law would force the same final state and output after their shared continuation. Correctness would contradict the certificate, so the reached-state map is injective and the state count is bounded below."))),
            DescribeRole.Theorem))));

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

    private static Formula LowerBoundFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("M"), Comma, Sp, F.Id("D"), Comma, Sp,
        F.Id("T"), Comma, Sp, F.Id("c"), Colon,
        RowBreak, Grp(),
        Call("DistinguishingFamily", F.Id("D"), F.Id("T"), F.Id("I"))
            , Sp, Land, Sp,
        Call("CorrectOn", F.Id("M"), F.Id("D"), F.Id("T")),
        Sp, Rightarrow, Sp,
        Call("card", F.Id("I")), Sp, Leq, Sp,
        Call("card", F.Id("S")), Dot,
        End, Grp(F.Id("gathered"))));

}
