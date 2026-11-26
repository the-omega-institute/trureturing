using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TraceLeviDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/coriperrin1985traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common four-factor arrangement characterizes equality of two concatenated traces.",
        H("Generalized Levi Factorization of Finite Traces"),
        Blocks(
            Paragraph(Text("Fix an arbitrary universe level u, used below as a universe "
                + "metaparameter. Let alpha be any type in Type(u), and let I be a symmetric "
                + "irreflexive relation on alpha. A word is a native finite list over alpha; "
                + "append denotes list concatenation and Mem(a,w) denotes native List.Mem and means that a occurs "
                + "in w. Connected denotes D5.S1.Words.TraceProjection.Connected: the "
                + "reflexive transitive closure of the contextual step exchanging "
                + "l ++ a :: b :: k with l ++ b :: a :: k when I(a,b), with the same "
                + "left and right contexts. It is not an additional supplied path or "
                + "a separately chosen quotient relation.")),
            Describe.Lean(
                DescribeId.Create("trace-levi-connected-append"),
                DeclarationHandle.Create("D5/S1/Words/TraceLevi.connected_append_iff"),
                H("A simultaneous two-by-two factorization"),
                StatementSource.FromAuthor(LeviStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every four words x,y,z,t, a connection from x ++ y "
                        + "to z ++ t is equivalent to the existence of four common words "
                        + "p,q,r,s. The row factors are x connected to p ++ q and y connected "
                        + "to r ++ s; the column factors are z connected to p ++ r and t "
                        + "connected to q ++ s. The same four words satisfy all four "
                        + "connections simultaneously. Every letter a of q and every letter "
                        + "b of r must satisfy I(a,b). This is a condition on each crossing "
                        + "pair of letters, and is stronger than asking only for a connection "
                        + "between q ++ r and r ++ q. Irreflexivity excludes a common letter "
                        + "from these two crossing factors.")),
                    Paragraph(Text("The statement includes empty alphabets, empty words and "
                        + "factors, infinite alphabets, and repeated letters. It assumes no "
                        + "finite alphabet, nonempty alphabet, decidable equality, occurrence "
                        + "matching, heap, partial order, schedule, or cut refinement. The "
                        + "four factors are existential conclusions, not input data.")),
                    Paragraph(Text("Cori and Perrin's Proposition 1.3 and its full proof on "
                        + "printed page 25 give the established four-factor arrangement for "
                        + "a finite alphabet A and a reflexive symmetric commutation relation "
                        + "theta. Their factors u,v,r,s correspond here to p,q,r,s. Their "
                        + "absolute commutation condition on v and r requires theta(a,b) "
                        + "for all crossing letters. Two obligations distinguish the present "
                        + "formulation from that source. First, the finite-alphabet congruence "
                        + "formulation must be related to the native contextual closure for "
                        + "arbitrary alpha. Second, the factors must satisfy the strict "
                        + "condition I(a,b) even though the reflexive source convention, "
                        + "theta(a,b) defined as a=b or I(a,b), also permits equality. The "
                        + "source telescope therefore does not directly supply the displayed "
                        + "native statement. No originality, effectiveness, complexity bound, "
                        + "or physical-history interpretation is asserted."))),
                DescribeRole.Theorem))));

    private static Formula LeviStatement()
    {
        var alphabet = V("alpha");
        var word = Call("List", alphabet);
        var crossing = All("a", alphabet,
            Implication(Call("Mem", V("a"), V("q")),
                All("b", alphabet,
                    Implication(Call("Mem", V("b"), V("r")),
                        Call("I", V("a"), V("b"))))));
        Formula factors = Q(
            Call("Connected", V("I"), V("x"), Call("append", V("p"), V("q"))), Land,
            Call("Connected", V("I"), V("y"), Call("append", V("r"), V("s"))), Land,
            Call("Connected", V("I"), V("z"), Call("append", V("p"), V("r"))), Land,
            Call("Connected", V("I"), V("t"), Call("append", V("q"), V("s"))), Land,
            Seq(Open, crossing, Close));
        foreach (var name in new[] { "s", "r", "q", "p" })
            factors = new Formula.Bind(FormulaQuantifier.Exists,
                FormulaIdentifier.Create(name), word, factors);
        Formula result = Q(
            Call("Connected", V("I"), Call("append", V("x"), V("y")),
                Call("append", V("z"), V("t"))), Iff,
            Seq(Open, factors, Close));
        foreach (var name in new[] { "t", "z", "y", "x" })
            result = All(name, word, result);
        var symmetry = All("a", alphabet, All("b", alphabet,
            Implication(Call("I", V("a"), V("b")), Call("I", V("b"), V("a")))));
        var irreflexivity = All("a", alphabet, new Formula.Not(Call("I", V("a"), V("a"))));
        return Disp(All("alpha", Call("Type", V("u")),
            All("I", new Formula.TypeArrow(alphabet, new Formula.TypeArrow(alphabet, V("Prop"))),
                Implication(symmetry, Implication(irreflexivity, result)))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Seq(Open, premise, Close), FormulaLogicOperator.Implies,
            Seq(Open, conclusion, Close));

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
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
