using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class FiniteSubsetMergingBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform pairwise length bound controls synchronization of finite uncertainty sets.",
        H("Quantitative Finite Subset Merging"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-subset-merging-length-bound"),
            DeclarationHandle.Create(
                "D5/S1/Words/FiniteSubsetMergingBound.exists_merging_word_length_le"),
            H("A merging word of length at most one pair budget per additional state"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature("cerny1964homogeneous"),
            Blocks(
                Paragraph(Text(
                    "The state type X and letter type A range independently over arbitrary universes. The function t is any deterministic transition, L is a natural number, and S is a finite set of states. The notation run(t,w,x) means the native list left fold w.foldl t x, and length(w) is the list length. Natural subtraction is truncated at zero.")),
                Paragraph(Text(
                    "Assume every pair of ambient states can be merged by some word of length at most L. Then a single word of length at most (card(S) minus one) times L merges every pair in S. There are no finiteness, nonemptiness or decidable equality assumptions on either ambient type. Empty state or letter types, empty and singleton uncertainty sets, L equal to zero, and infinite ambient types are included.")),
                Paragraph(Text(
                    "Induct on the finite set. The empty set uses the empty word. For an inserted state a and a nonempty old set, first apply the old merging word u and choose an old representative b. Apply the pairwise hypothesis to the two states run(t,u,a) and run(t,u,b), obtaining v. The concatenation of u and v merges the inserted state with every old state; equality of old images is preserved by folding v. Its length is at most (card(S) minus one) times L plus L, hence card(S) times L. If the old set is empty, the inserted singleton again uses the empty word.")),
                Paragraph(Text(
                    "Černý's Theorem 2 gives the successive pair-merging mechanism for finite automata. The statement here exposes its uniform length estimate for a finite uncertainty set in an arbitrary ambient transition system."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Run(string word, string state) =>
        Call("run", F.Id("t"), F.Id(word), F.Id(state));

    private static Formula Statement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("X"), Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
        F.Id("A"), Colon, Sp, Call("Type", F.Id("v")), Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("t"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, F.Id("X"), Comma, Sp,
        F.Id("L"), Colon, Sp, Call("Nat"), Comma, Sp,
        F.Id("S"), Colon, Sp, Call("Finset", F.Id("X")), Comma,
        RowBreak, Grp(),
        Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("X"), Comma, Sp,
        Exists, Sp, F.Id("p"), Colon, Sp, Call("List", F.Id("A")), Comma, Sp,
        Call("length", F.Id("p")), Sp, Leq, Sp, F.Id("L"), Sp, Land, Sp,
        Run("p", "x"), Sp, Eq, Sp, Run("p", "y"), Close,
        RowBreak, Grp(), Rightarrow, Sp,
        Exists, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("A")), Comma, Sp,
        Call("length", F.Id("w")), Sp, Leq, Sp,
        Open, Call("card", F.Id("S")), Sp, Minus, Sp, D(1), Close,
        Sp, Star, Sp, F.Id("L"), Sp, Land,
        RowBreak, Grp(),
        Forall, Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
        Forall, Sp, F.Id("y"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
        Run("w", "x"), Sp, Eq, Sp, Run("w", "y"), Dot,
        End, Grp(F.Id("gathered"))));
}
