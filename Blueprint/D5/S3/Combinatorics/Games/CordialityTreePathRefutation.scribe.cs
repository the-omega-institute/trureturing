using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Games;

internal sealed class CordialityTreePathRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Games/CordialityTreePathRefutation.";
    private const string Note = "D5/L/GraphInvariants/kropmittalwigal2024cordiality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tree on ten vertices forces discrepancy at least three, while Admirable "
            + "can hold the path on ten vertices to discrepancy at most one.",
        H("A Tree Exceeds the Path in the Cordiality Game"),
        Blocks(
            Definition("free", "Unlabelled vertices", All(F.Id("n"), Nat,
                All(F.Id("A"), Sets, All(F.Id("B"), Sets,
                    Seq(Call("free", F.Id("A"), F.Id("B")), Eq,
                        Qualified("Finset", "univ"), Setminus, Sp,
                        Parenthesized(Seq(F.Id("A"), Cup, Sp, F.Id("B"))))))),
                "The disjoint sets A and B record the vertices already labelled zero "
                    + "and one. Their complement consists of the legal next moves.", false),
            Definition("e1", "Edges labelled one", GraphState(
                Seq(Call("e1", F.Id("G"), F.Id("A")), Eq, EdgeCount())),
                "Section 1, page 2: \"The labels on edges are then determined by the sum "
                    + "of incident vertex labels modulo 2.\" Vertices are Fin n. A is the "
                    + "zero-labelled set, so the filter counts each undirected edge with "
                    + "oppositely labelled endpoints once.", true),
            Definition("e0", "Edges labelled zero", GraphState(
                Seq(Call("e0", F.Id("G"), F.Id("A")), Eq,
                    Field(Field(F.Id("G"), "edgeFinset"), "card"), Minus,
                    Call("e1", F.Id("G"), F.Id("A")))),
                "Section 1, page 2: \"In other words, after all the vertices are labeled, "
                    + "if we let e₀ be the number of edges labeled by 0 and e₁ be the number "
                    + "of edges labeled by 1, then we define the discrepancy to be d = |e₁ − e₀|.\" "
                    + "Subtraction here is "
                    + "natural-number subtraction. Every edge has exactly one of the two labels.", true),
            Definition("discrepancy", "Terminal discrepancy", GraphState(
                Seq(Call("discrepancy", F.Id("G"), F.Id("A")), Eq,
                    App(Qualified("Int", "natAbs"),
                        Seq(Parenthesized(Seq(Call("e1", F.Id("G"), F.Id("A")), Colon, Integers)),
                            Minus, Parenthesized(Seq(Call("e0", F.Id("G"), F.Id("A")),
                                Colon, Integers)))))),
                "Section 1, page 2: \"then we define the discrepancy to be d = |e₁ − e₀|. "
                    + "Then Admirable attempts to minimize d and Impish attempts to maximize d.\" "
                    + "The two counts are coerced from naturals to integers before subtraction. "
                    + "At a terminal state B is the complement of A.", true),
            Definition("gameValue", "Backward induction", All(F.Id("n"), Nat,
                All(F.Id("G"), Call("SimpleGraph", Vertices), GraphInstance(F.Id("G"),
                    All(F.Id("A"), Sets, All(F.Id("B"), Sets,
                        Seq(Call("gameValue", F.Id("G"), F.Id("A"), F.Id("B")), Eq,
                            F.Id("if"), Sp,
                            Parenthesized(Seq(Call("free", F.Id("A"), F.Id("B")), Eq, Emptyset)),
                            Sp, F.Id("then"), Sp, Call("discrepancy", F.Id("G"), F.Id("A")),
                            Sp, F.Id("else"), Sp, F.Id("if"), Sp,
                            Parenthesized(Seq(Field(F.Id("A"), "card"), Eq, Field(F.Id("B"), "card"))),
                            Sp, F.Id("then"), Sp, MoveValues(true), Sp, F.Id("else"), Sp,
                            MoveValues(false))))))),
                "Section 1, page 2: \"Admirable labels selected vertices by 0 and Impish "
                    + "labels selected vertices by 1.\" The initial state is empty and "
                    + "Admirable moves first. Equal cardinals mean Admirable moves and "
                    + "takes the minimum; otherwise Impish takes the maximum. The recursion "
                    + "decreases the number of unlabelled vertices. Nonempty-set proof "
                    + "arguments to min' and max' are implicit in the display. Strong induction "
                    + "proves that either player's guaranteed discrepancy bounds this value.", true),
            Definition("cg", "Game cordiality number", All(F.Id("n"), Nat,
                All(F.Id("G"), Call("SimpleGraph", Vertices), GraphInstance(F.Id("G"),
                    Seq(Call("cg", F.Id("G")), Eq,
                        Call("gameValue", F.Id("G"), Emptyset, Emptyset))))),
                "Section 1, page 2: \"We define the game cordiality number, c_g(G), to be "
                    + "the value of d when both players play optimally. Further, to prove our "
                    + "claimed bounds, we create a variant of the cordiality game where Impish "
                    + "starts rather than Admirable.\" Thus cg is the Admirable-starts value.", true),
            Definition("claim", "The tree–path conjecture",
                Seq(Call("claim"), Iff, Sp, All(F.Id("n"), Nat,
                    All(F.Id("T"), Call("SimpleGraph", Vertices), GraphInstance(F.Id("T"),
                        GraphInstance(App(Qualified("SimpleGraph", "pathGraph"), F.Id("n")),
                            Seq(Field(F.Id("T"), "IsTree"), Longrightarrow, Sp,
                                Call("cg", F.Id("T")), Le, Sp,
                                Call("cg", App(Qualified("SimpleGraph", "pathGraph"), F.Id("n"))))))))),
                "Section 3, Conjecture 3.2, page 9: \"For any tree T of order n, "
                    + "c_g(T) ≤ c_g(P_n).\" The encoding uses every natural n and every "
                    + "SimpleGraph on Fin n. IsTree is Mathlib's tree predicate. The two "
                    + "anonymous DecidableRel arguments express decidability of the "
                    + "adjacency relations and preserve this quantification.", true),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A ten-vertex counterexample"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Call("claim")))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Take the tree with edges {i,i+1} for i from zero "
                    + "through six, together with {0,8} and {0,9}. Explicit walks establish "
                    + "connectivity, and its nine edges establish that it is a tree. Impish "
                    + "pairs (0,4), (1,5), (2,6), (3,7), and (8,9), responding to each "
                    + "Admirable move with its partner. The pairing is legal and preserves "
                    + "disjointness. Every terminal transversal has discrepancy at least "
                    + "three. Strong induction transfers that bound to the minimax value. "
                    + "For the path on ten vertices, an explicit finite strategy table "
                    + "and its recursive soundness theorem bound the value above by one. "
                    + "The conjectured comparison would therefore imply three is at most one."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, Formula formula,
        string text, bool literature) => Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))
                : AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))));

    private static Formula Nat => Seq(Mathbb, Sp, F.Id("N"));
    private static Formula Integers => Seq(Mathbb, Sp, F.Id("Z"));
    private static Formula Vertices => Call("Fin", F.Id("n"));
    private static Formula Sets => Call("Finset", Vertices);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Field(Formula value, string name) => Seq(value, Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : Seq(function, Parenthesized(Join(args)));
    private static Formula Join(Formula[] args) => Seq(args.SelectMany(
        (arg, index) => index == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray());
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp, body);
    private static Formula GraphInstance(Formula graph, Formula body) =>
        Seq(OpenBracket, Call("DecidableRel", Field(graph, "Adj")), CloseBracket, Sp, body);
    private static Formula GraphState(Formula body) => All(F.Id("n"), Nat,
        All(F.Id("G"), Call("SimpleGraph", Vertices), GraphInstance(F.Id("G"), All(F.Id("A"), Sets, body))));
    private static Formula ExistsIn(Formula variable, Formula type, Formula set, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp,
            Parenthesized(Seq(variable, InMacro, Sp, set)), Land, Sp, Parenthesized(body));
    private static Formula EdgeCount()
    {
        var crossing = Seq(Parenthesized(Seq(F.Id("u"), InMacro, Sp, F.Id("A"))),
            Land, Sp, Parenthesized(Seq(Neg, Sp,
                Parenthesized(Seq(F.Id("v"), InMacro, Sp, F.Id("A"))))));
        var condition = ExistsIn(F.Id("u"), Vertices, F.Id("e"),
            ExistsIn(F.Id("v"), Vertices, F.Id("e"), crossing));
        var predicate = Seq(F.Id("fun"), Sp,
            Parenthesized(Seq(F.Id("e"), Colon, Call("Sym2", Vertices))), Sp, Mapsto, Sp, condition);
        return Field(App(Field(Field(F.Id("G"), "edgeFinset"), "filter"), predicate), "card");
    }
    private static Formula MoveValues(bool admirable)
    {
        var remaining = Call("free", F.Id("A"), F.Id("B"));
        var vertex = Seq(F.Id("v"), Dot, D(1));
        var values = App(Field(Field(remaining, "attach"), "image"),
            Seq(F.Id("fun"), Sp, F.Id("v"), Sp, Mapsto, Sp,
                Call("gameValue", F.Id("G"),
                    admirable ? App(Qualified("Finset", "insert"), vertex, F.Id("A")) : F.Id("A"),
                    admirable ? F.Id("B") : App(Qualified("Finset", "insert"), vertex, F.Id("B")))));
        return Seq(Parenthesized(values), Dot, Named(admirable ? "min" : "max"), Apos);
    }
}
