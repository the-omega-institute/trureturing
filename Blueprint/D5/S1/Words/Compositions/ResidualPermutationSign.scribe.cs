using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ResidualPermutationSignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/ResidualPermutationSign.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/codex2026a392714residual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interlaced prefix intervals have signed permutation sum supported only at identity.",
        H("Residual Permutation Sign Cancellation"),
        Blocks(
            Paragraph(Text("Let a and b permute the positive integers from 1 to n. "
                + "Write A and B for their prefix sums, starting at zero. The Lean "
                + "permutations act on Fin n, so each value is increased by one when "
                + "forming a prefix sum. The empty permutation is included. All sums "
                + "of parity signs below take values in the integers.")),
            Node("prefixSum", "Positive prefix sums", Disp(Q(
                Call("prefixSum", V("p"), V("k")), Eq,
                Sum, Underscore, Grp(Q(D(0), Le, V("j"), Lt, V("n"), Comma, V("j"), Lt, V("k"))),
                Par(Q(Call("p", V("j")), Plus, D(1))))),
                "The argument k is a prefix length. The summation includes exactly "
                + "the indices j in Fin n with j less than k.", DescribeRole.Definition),
            Node("Upper", "Upper bounds", Disp(Q(Call("Upper", V("a"), V("b")), Iff,
                Forall, V("i"), Comma, D(0), Le, V("i"), Le, V("n"), Implies,
                Sub("B", V("i")), Le, Sub("A", V("i")))),
                "Upper compares all prefix sums up to length n.", DescribeRole.Definition),
            Node("LowerFrom", "Remaining lower bounds", Disp(Q(
                Call("LowerFrom", V("a"), V("b"), V("r")), Iff,
                Forall, V("i"), Comma, V("r"), Lt, V("i"), Le, V("n"), Implies,
                Sub("A", Q(V("i"), Minus, D(1))), Lt, Sub("B", V("i")))),
                "Here i is the one-based prefix length. LowerFrom r retains the "
                + "strict lower cuts at lengths r+1 through n.", DescribeRole.Definition),
            Node("signInt", "Integer parity sign", Disp(Q(
                Call("signInt", V("b")), Eq, Call("sign", V("b")))),
                "The usual permutation sign is coerced to the integers.", DescribeRole.Definition),
            Node("rowSum", "Signed sum with initial lower cuts removed", Disp(Q(
                Row(V("r")), Eq, SignedSum(Q(Call("Upper", V("a"), V("b")), Land,
                    Call("LowerFrom", V("a"), V("b"), V("r")))))),
                "R at r sums over all b with every upper bound and the lower bounds "
                + "remaining from r onward.", DescribeRole.Definition),
            Node("lower_cut_removal", "Removing one lower cut", Disp(Q(
                Forall, V("r"), InMacro, Nat(), Comma,
                Row(V("r")), Eq, Row(Q(V("r"), Plus, D(1))))),
                "For r=0 positivity makes the first cut automatic. For 0<r<n the "
                + "newly admitted terms have B at r+1 at most A at r. Swap positions "
                + "r and r+1, using one-based positions. Only the prefix of length r "
                + "changes, and it remains at most B at r+1. Later lower bounds are "
                + "unchanged. This fixed transposition pairs the new terms with "
                + "opposite signs. For r at least n there is no remaining cut.", DescribeRole.Theorem),
            Node("upper_sum_vanish", "Cancelling the upper-bound class", Disp(Q(
                V("a"), Neq, V("id"), Implies,
                SignedSum(Call("Upper", V("a"), V("b"))), Eq, D(0))),
                "Choose the least moved index k of a, and let j>k be the position "
                + "of value k. Every upper-admissible b fixes the indices before k. "
                + "The entries at positions j-1 and j are therefore at least k. "
                + "Swapping these positions preserves the only affected upper bound, "
                + "since B at j is at most A at j-1 plus k. This transposition is "
                + "independent of b and reverses its sign.", DescribeRole.Theorem),
            Node("InResidual", "The interlaced intervals", Disp(Q(
                Call("InResidual", V("a"), V("b")), Iff, Forall, V("i"), Comma,
                D(1), Le, V("i"), Le, V("n"), Implies,
                Sub("A", Q(V("i"), Minus, D(1))), Lt, Sub("B", V("i")),
                Le, Sub("A", V("i")))),
                "This is precisely membership in L(a). The left inequality is "
                + "strict and the right inequality is weak.", DescribeRole.Definition),
            Node("signed_residual_sum", "The residual sign identity", Disp(Q(
                SignedSum(Call("InResidual", V("a"), V("b"))), Eq,
                OpenBracket, V("a"), Eq, V("id"), CloseBracket)),
                "The brackets denote 1 when a is the identity and 0 otherwise. "
                + "Iterate lower-cut removal to reduce the sum to Upper. For the "
                + "identity, the smallest unused positive value at each position "
                + "forces b to be the identity. For any other a the upper sum "
                + "vanishes by the fixed transposition just constructed. This proves "
                + "the identity for every n and every a, without additional hypotheses.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("residual-sign-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Q(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Q(Open, value, Close);
    private static Formula Sub(string name, Formula index) => Q(V(name), Underscore, Grp(index));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Row(Formula index) => Q(Sub("R", index), Par(V("a")));
    private static Formula SignedSum(Formula predicate) => Q(Sum, Underscore,
        Grp(Q(V("b"), InMacro, Sub("S", V("n")), Colon, predicate)), Call("sign", V("b")));
}
