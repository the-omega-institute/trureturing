using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class FriedenSortingNetworkDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/FriedenSortingNetwork.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/frieden2026bigcactus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological restrictions of reduced reversal words.",
        H("A four-wire obstruction in a sorting network"),
        Blocks(
            Paragraph(Text("A state lists the wire labels at their current positions. The generator "
                + "with zero-based index i swaps positions i and i+1. A reduced reversal word "
                + "starts at the identity, ends at the reversal and has length n(n-1)/2 "
                + "with natural-number division. Every unordered pair of labels crosses once, "
                + "from increasing to decreasing order. In the formulas, n is natural, "
                + "i and j are generators, p is a state, S is a finite set of labels, a is a "
                + "label, and u, m, v and w are words on n wires.")),
            Definition("Word", "Adjacent-swap words", AtRank(Equal(WordType(), Call("List", Generator()))),
                "Finite lists of generators with zero-based indices below n-1."),
            Definition("State", "Wire state", AtRank(Equal(StateType(), Call("Perm", LabelType()))),
                "A permutation sending each position to the label currently there."),
            Definition("Orientation", "Path orientation",
                AtRank(Equal(Call("Orientation", V("n")),
                    Q(Call("Fin", Q(V("n"), Minus, D(2))), To, Name("Bool")))),
                "One Boolean for each edge between consecutive generators."),
            Definition("left", "Left position",
                AtRank(HasType(Call("left", V("i")), LabelType()), ("i", Generator())),
                "The position whose index is the generator's index."),
            Definition("right", "Right position",
                AtRank(HasType(Call("right", V("i")), LabelType()), ("i", Generator())),
                "The position one greater than the generator's index."),
            Definition("step", "Adjacent swap",
                AtRank(Equal(Call("step", V("p"), V("i")),
                    Q(V("p"), Circ, Call("swap", Call("left", V("i")), Call("right", V("i"))))),
                    ("p", StateType()), ("i", Generator())),
                "Swap the two positions before reading their labels in the current state."),
            Definition("endpoints", "Crossing endpoints",
                AtRank(Equal(Call("endpoints", V("p"), V("i")),
                    Parenthesized(Q(Label("left"), Comma, Label("right")))),
                    ("p", StateType()), ("i", Generator())),
                "The labels at the two positions before the swap, ordered left to right."),
            Definition("crossingPairsFrom", "Chronological crossing pairs",
                AtRank(HasType(Call("crossingPairsFrom", V("p"), V("w")),
                    Call("List", Q(LabelType(), Times, LabelType()))),
                    ("p", StateType()), ("w", WordType())),
                "Record both labels before each swap while advancing the state through the word."),
            Definition("restrictFrom", "Restriction from a state",
                AtRank(HasType(Call("restrictFrom", V("S"), V("p"), V("w")),
                    Call("List", Naturals())), ("S", LabelSet()), ("p", StateType()), ("w", WordType())),
                "Advance the state at every swap. Record a letter only when both labels lie in the selected set. "
                + "Use one plus the number of selected labels strictly to the left of the swapped positions.",
                literature: true),
            Definition("restrict", "Induced subnetwork",
                AtRank(Equal(Call("restrict", V("w"), V("S")),
                    Call("restrictFrom", V("S"), Name("id"), V("w"))),
                    ("w", WordType()), ("S", LabelSet())),
                "Start the restriction at the identity state.", literature: true),
            Definition("forbidden", "The four forbidden words",
                Equal(Name("forbidden"), ListOf(WordDigits(1, 2, 3, 2, 1, 2), WordDigits(3, 2, 1, 2, 3, 2),
                    WordDigits(2, 1, 2, 3, 2, 1), WordDigits(2, 3, 2, 1, 2, 3))),
                "The one-based chronological words 123212, 321232, 212321 and 232123.", literature: true),
            Definition("AvoidsX", "Four-wire avoidance",
                AtRank(Q(Call("AvoidsX", V("w")), Sp, Iff, Sp,
                    Bind(FormulaQuantifier.ForAll, "S", LabelSet(), Q(Equal(Call("card", V("S")), D(4)),
                        Sp, Implies, Sp, Neg, Parenthesized(Q(Call("restrict", V("w"), V("S")),
                            Sp, InMacro, Sp, Name("forbidden")))))), ("w", WordType())),
                "Every four-element set of labels gives a restriction outside forbidden.", literature: true),
            Definition("ReducedReversal", "Reduced reversal word",
                AtRank(Q(Call("ReducedReversal", V("w")), Sp, Iff, Sp,
                    Equal(Call("length", V("w")), Q(Lfloor, Sp, V("n"), Cdot,
                        Parenthesized(Q(V("n"), Minus, D(1))), Slash, D(2), Rfloor)), Sp, Land, Sp,
                    Equal(Call("foldl", Name("step"), Name("id"), V("w")), Name("revPerm"))),
                    ("w", WordType())),
                "The length is n(n-1)/2 in natural numbers, and folding step from the identity gives the reversal."),
            Definition("below", "Selected predecessors",
                AtRank(HasType(Call("below", V("S"), V("p"), V("a")), LabelSet()),
                    ("S", LabelSet()), ("p", StateType()), ("a", LabelType())),
                "The selected labels strictly to the left of the given label."),
            Definition("rank", "Rank in the selected order",
                AtRank(Equal(Call("rank", V("S"), V("p"), V("a")),
                    Call("card", Call("below", V("S"), V("p"), V("a")))),
                    ("S", LabelSet()), ("p", StateType()), ("a", LabelType())),
                "The cardinality of the selected predecessor set."),
            Definition("wireDirections", "Chronological movements of a wire",
                AtRank(HasType(Call("wireDirections", V("p"), V("a"), V("w")), Call("List", Name("Bool"))),
                    ("p", StateType()), ("a", LabelType()), ("w", WordType())),
                "Keep the swaps involving the given label. Record true for a move right and false for a move left."),
            Node("left_ne_right", "Distinct endpoints of a generator",
                AtRank(Q(Call("left", V("i")), Sp, Neq, Sp, Call("right", V("i"))),
                    ("i", Generator())),
                "The two positions have indices i and i+1.", AssessedProvenance.FromRepo()),
            Node("restrict_cons", "Rank of a retained crossing",
                AtRank(Equal(Call("restrictFrom", V("S"), V("p"), Cons(V("i"), V("w"))),
                    Call("ite", Selected(), Cons(
                            Add(Call("rank", V("S"), V("p"), Label("left")), D(1)), RestrictedTail()),
                        RestrictedTail())),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator()), ("w", WordType())),
                "The recursive restriction always advances the full state. It prepends the stated "
                + "one-based letter precisely when both swapped labels belong to S. Rank counts "
                + "selected labels strictly to the left of the left endpoint. This is the "
                + "chronological subnetwork construction in Section 4.4.",
                AssessedProvenance.FromRepo(Source)),
            Node("rank_right_before", "Ranks at adjacent positions with the left wire selected",
                AtRank(Q(Call("p", Call("left", V("i"))), Sp, InMacro, Sp, V("S"), Sp, Implies, Sp,
                    Equal(Call("rank", V("S"), V("p"), Call("p", Call("right", V("i")))),
                        Add(Call("rank", V("S"), V("p"), Call("p", Call("left", V("i")))), D(1)))),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator())),
                "The left endpoint adds exactly one selected label to the rank of the right endpoint.",
                AssessedProvenance.FromRepo()),
            Node("quartet_left", "A repeated left generator forces a forbidden restriction",
                AtRank(Q(Parenthesized(Q(Add(Value("i"), D(2)), Lt, V("n"), Sp, Land, Sp,
                    Parenthesized(Bind(FormulaQuantifier.ForAll, "j", Generator(), Q(
                        V("j"), Sp, InMacro, Sp, V("m"), Sp, Implies, Sp,
                        Value("j"), Sp, Neq, Sp, Value("i"), Sp, Land, Sp, Value("j"), Sp, Neq, Sp,
                        Add(Value("i"), D(1))))), Sp, Land, Sp,
                    Call("ReducedReversal", RepeatedWord()))), Sp, Implies, Sp,
                    Parenthesized(Bind(FormulaQuantifier.Exists, "S", LabelSet(),
                        Q(Call("card", V("S")), Eq, D(4),
                        Sp, Land, Sp, Call("restrict", RepeatedWord(), V("S")), Sp,
                        InMacro, Sp, Name("forbidden"))))),
                    ("u", WordType()), ("m", WordType()), ("v", WordType()), ("i", Generator())),
                "The repeated word is u followed by i, m, i and v. The right block is nonempty "
                + "when the index of i plus two is below n. The middle list m omits i and the "
                + "generator with index one greater than i. Between the two uses of "
                + "i, the wire at position i+1 stays fixed and the labels strictly to its "
                + "right stay in that block. The two endpoint swaps and the unique intervening "
                + "crossing in the left block yield letters 2, 1, 2. Choose one wire in the "
                + "right block. It moves only right in the retained prefix and only left in "
                + "the retained suffix. Its initial rank determines the complete restriction, "
                + "one of 123212, 232123, 321232 and 212321.", AssessedProvenance.FromRepo(Source)),
            Node("rank_step_stay", "Rank at a dropped swap",
                AtRank(Q(Parenthesized(Q(V("a"), Sp, InMacro, Sp, V("S"), Sp, Land, Sp,
                        Neg, Parenthesized(Selected()))), Sp, Implies, Sp,
                    Equal(Call("rank", V("S"), Call("step", V("p"), V("i")), V("a")),
                        Call("rank", V("S"), V("p"), V("a")))),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator()), ("a", LabelType())),
                "For each selected wire a, dropping a swap means at least one of its endpoints "
                + "is unselected. No two selected wires change relative order.",
                AssessedProvenance.FromRepo()),
            Node("rank_step_move_right", "Rank after a move to the right",
                AtRank(Q(Call("p", Call("right", V("i"))), Sp, InMacro, Sp, V("S"), Sp, Implies, Sp,
                    Equal(Call("rank", V("S"), Call("step", V("p"), V("i")),
                            Call("p", Call("left", V("i")))),
                        Add(Call("rank", V("S"), V("p"), Call("p", Call("left", V("i")))), D(1)))),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator())),
                "The left wire gains one selected predecessor when it crosses a selected right wire.",
                AssessedProvenance.FromRepo()),
            Node("rank_step_move_left", "Rank after a move to the left",
                AtRank(Q(Call("p", Call("left", V("i"))), Sp, InMacro, Sp, V("S"), Sp, Implies, Sp,
                    Equal(Call("rank", V("S"), Call("step", V("p"), V("i")),
                            Call("p", Call("right", V("i")))),
                        Call("rank", V("S"), V("p"), Call("p", Call("left", V("i")))))),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator())),
                "The right wire takes the previous rank of the selected left wire.",
                AssessedProvenance.FromRepo()),
            Node("rank_other", "Rank of a wire outside the swap",
                AtRank(Q(Parenthesized(Q(Label("left"), Sp, Neq, Sp, V("a"), Sp, Land, Sp,
                        Label("right"), Sp, Neq, Sp, V("a"))), Sp, Implies, Sp,
                    Equal(Call("rank", V("S"), Call("step", V("p"), V("i")), V("a")),
                        Call("rank", V("S"), V("p"), V("a")))),
                    ("S", LabelSet()), ("p", StateType()), ("i", Generator()), ("a", LabelType())),
                "A label distinct from both swapped labels preserves its order relative to "
                + "each selected wire.",
                AssessedProvenance.FromRepo()),
            Node("wire_directions_bound", "Number of moves of a wire",
                AtRank(Q(Call("ReducedReversal", V("w")), Sp, Implies, Sp,
                    Call("length", Call("wireDirections", Name("id"), V("a"), V("w"))),
                    Sp, Le, Sp, V("n"), Minus, D(1)), ("w", WordType()), ("a", LabelType())),
                "For each wire a, each move has a distinct partner, and the partners all lie "
                + "among the other n-1 wire labels.", AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("frieden-network-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose,
        bool literature = false) => Describe.Lean(
        DescribeId.Create("frieden-network-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Selected() =>
        Q(Label("left"), Sp, InMacro, Sp, V("S"), Sp, Land, Sp, Label("right"), Sp, InMacro, Sp, V("S"));

    private static Formula AtRank(Formula body, params (string Name, Formula Type)[] binders)
    {
        for (var index = binders.Length - 1; index >= 0; index--)
        {
            body = Bind(FormulaQuantifier.ForAll, binders[index].Name, binders[index].Type, body);
        }
        return Bind(FormulaQuantifier.ForAll, "n", Naturals(), body);
    }

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);

    private static Formula Generator() => Call("Fin", Q(V("n"), Minus, D(1)));
    private static Formula LabelType() => Call("Fin", V("n"));
    private static Formula LabelSet() => Call("Finset", LabelType());
    private static Formula StateType() => Call("State", V("n"));
    private static Formula WordType() => Call("Word", V("n"));
    private static Formula Naturals() => Q(Mathbb, Grp(V("N")));
    private static Formula HasType(Formula value, Formula type) => Q(value, Sp, Colon, Sp, type);
    private static Formula ListOf(params Formula[] elements)
    {
        var parts = new Formula[elements.Length * 2 + 1];
        parts[0] = OpenBracket;
        for (var index = 0; index < elements.Length; index++)
        {
            parts[index * 2 + 1] = elements[index];
            parts[index * 2 + 2] = Comma;
        }
        parts[^1] = CloseBracket;
        return Q(parts);
    }

    private static Formula WordDigits(byte a, byte b, byte c, byte d, byte e, byte f) =>
        ListOf(D(a), D(b), D(c), D(d), D(e), D(f));
    private static Formula Parenthesized(Formula body) => Q(Open, body, Close);
    private static Formula Label(string endpoint) => Call("p", Call(endpoint, V("i")));
    private static Formula RestrictedTail() => Call("restrictFrom", V("S"), Call("step", V("p"), V("i")), V("w"));
    private static Formula Cons(Formula head, Formula tail) => Q(head, Sp, Colon, Colon, Sp, tail);
    private static Formula Value(string letter) => Q(V(letter), Dot, Name("val"));
    private static Formula RepeatedWord() =>
        Q(V("u"), Sp, Plus, Plus, Sp, Parenthesized(Cons(V("i"),
            Q(V("m"), Sp, Plus, Plus, Sp, Cons(V("i"), V("v"))))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(params Formula[] items) => Seq(items);
    private static Formula Name(string name) => Q(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name == "p" ? V(name) : Name(name), [.. args]);
}
