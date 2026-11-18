using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class FiniteSubsetCompressionBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local reductions of finite uncertainty sets give a cumulative bound with arbitrary costs at each rank.",
        H("Rank-Dependent Finite Subset Compression"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-subset-compression-length-bound"),
            DeclarationHandle.Create(
                "D5/S1/Words/FiniteSubsetCompressionBound.exists_compressing_word_length_le"),
            H("Summing local rank budgets produces one compressing word"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state type X and letter type A range independently over arbitrary universes. The original decidable equality on X is retained. The map t is a deterministic transition and C is any natural-valued cost function. Write image(t,w,S) for the finite image of S under x mapped to the native list left fold w.foldl t x, and length(w) for list length. All subtraction is natural subtraction truncated at zero.")),
                Paragraph(Text(
                    "Assume every finite uncertainty set T of at least two states admits a word of length at most C(card(T)) whose image has strictly smaller cardinality. Then every finite S admits a word reducing its image to at most one state, of length at most the sum of C(2), C(3), through C(card(S)). No monotonicity of C is required. The ambient state and letter types need not be finite or nonempty. Empty and singleton S use the empty word and have zero total budget.")),
                Paragraph(Text(
                    "Strongly induct on the current cardinality. Above one state, choose a reducing word u and let U be its actual image. Apply the induction hypothesis to U, obtaining v, and concatenate u followed by v. The fold of the concatenation has exactly the same image as applying v to U. Since card(U) is strictly smaller than card(T), its prefix sum is bounded by the prefix ending at card(T) minus one. Adding the cost C(card(T)) gives the required total. Ranks skipped by one reduction contribute nonnegative unused terms, which is why the argument does not need a monotone cost profile.")),
                Paragraph(Text(
                    "The uniform pairwise result FiniteSubsetMergingBound.exists_merging_word_length_le supplies a different input interface and the product estimate (card(S) minus one) times L. Here the local hypothesis directly concerns a strict reduction of the entire current image and can provide different budgets at different ranks. This permits applying rank-specific compression estimates in finite automata, and also applies to finite uncertainty sets in infinite deterministic transition systems. The conclusion gives a word length bound; it does not provide a cost for finding the local words, a shortest-word theorem, a noisy recovery guarantee, or an original-state reconstruction."))),
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

    private static Formula Image(string word, string set) =>
        Call("image", F.Id("t"), F.Id(word), F.Id(set));

    private static Formula Statement() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("X"), Colon, Sp, Call("Type", F.Id("u")), Comma, Sp,
        F.Id("A"), Colon, Sp, Call("Type", F.Id("v")), Comma, Sp,
        OpenBracket, Call("DecidableEq", F.Id("X")), CloseBracket, Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("t"), Colon, Sp, F.Id("X"), Sp, To, Sp,
        F.Id("A"), Sp, To, Sp, F.Id("X"), Comma, Sp,
        F.Id("C"), Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("S"), Colon, Sp, Call("Finset", F.Id("X")), Comma,
        RowBreak, Grp(),
        Open, Forall, Sp, F.Id("T"), Colon, Sp, Call("Finset", F.Id("X")), Comma, Sp,
        D(2), Sp, Leq, Sp, Call("card", F.Id("T")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("p"), Colon, Sp, Call("List", F.Id("A")), Comma,
        RowBreak, Grp(),
        Call("length", F.Id("p")), Sp, Leq, Sp, Call("C", Call("card", F.Id("T"))),
        Sp, Land, Sp, Call("card", Image("p", "T")), Sp, Lt, Sp,
        Call("card", F.Id("T")), Close,
        RowBreak, Grp(), Rightarrow, Sp,
        Exists, Sp, F.Id("w"), Colon, Sp, Call("List", F.Id("A")), Comma, Sp,
        Call("length", F.Id("w")), Sp, Leq, Sp,
        new Formula.Subscript(Sum, Seq(F.Id("k"), Sp, InMacro, Sp,
            Call("range", Seq(Call("card", F.Id("S")), Sp, Minus, Sp, D(1))))),
        Sp, Call("C", Seq(F.Id("k"), Sp, Plus, Sp, D(2))), Sp, Land,
        RowBreak, Grp(),
        Call("card", Image("w", "S")), Sp, Leq, Sp, D(1), Dot,
        End, Grp(F.Id("gathered"))));
}
