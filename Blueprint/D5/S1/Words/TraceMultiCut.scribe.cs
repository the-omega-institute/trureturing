using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TraceMultiCutDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/coriperrin1985traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One common pair of rows refines any finite ordered product of native traces.",
        H("Simultaneous Two-Row Refinement of Finite Trace Products"),
        Blocks(
            Paragraph(Text("Fix any universe level u as a universe metaparameter, any "
                + "alphabet alpha in Type(u), and a symmetric irreflexive relation I on "
                + "alpha. A word is a native finite List(alpha). Connected means exactly "
                + "D5.S1.Words.TraceProjection.Connected, the reflexive transitive closure "
                + "of the original contextual adjacent swap: l ++ a :: b :: t may be "
                + "exchanged with l ++ b :: a :: t when I(a,b). The contexts remain "
                + "unchanged. Mem is native list membership; append is concatenation; "
                + "flatten concatenates a list of words in order; ofFn lists a Fin-indexed "
                + "family in increasing order. The expression column(zs,j) is the native "
                + "list entry zs[j], and Fin(length(zs)) consists of all column indices.")),
            Describe.Lean(
                DescribeId.Create("trace-multi-cut-connected-append-flatten"),
                DeclarationHandle.Create("D5/S1/Words/TraceMultiCut.connected_append_flatten_iff"),
                H("A common refinement across every cut"),
                StatementSource.FromAuthor(MultiCutStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every pair of words x,y and every finite list of "
                        + "words zs, connection of x ++ y with flatten(zs) is equivalent "
                        + "to the existence of two families p,r on Fin(length(zs)). The "
                        + "same families satisfy every condition: x is connected to the "
                        + "concatenation of all p(j), y to that of all r(j), and each "
                        + "column zs[j] is connected to p(j) ++ r(j). Whenever j < k, "
                        + "every letter a in the later upper factor p(k) and every letter "
                        + "b in the earlier lower factor r(j) satisfy the strict relation "
                        + "I(a,b). Separate choices for the different cuts would not "
                        + "satisfy this simultaneous conclusion.")),
                    Paragraph(Text("Induct on the list of columns. The binary native Levi "
                        + "factorization splits the first column into p0,r0 and the "
                        + "remaining product into q,s. Apply the induction hypothesis "
                        + "once to q,s and the tail columns, then prepend p0,r0 to the "
                        + "resulting families. A letter in any later upper factor occurs "
                        + "in their concatenation and therefore in q, since native "
                        + "connection preserves letter membership. Binary Levi's strict "
                        + "independence of q and r0 then gives every crossing from the "
                        + "first lower factor to a later upper factor. The other "
                        + "crossings come from induction. Conversely, reconstruct the "
                        + "tail connection by induction and apply binary Levi to the "
                        + "first column and that tail, using the union of the prescribed "
                        + "crossing conditions.")),
                    Paragraph(Text("If zs is empty, membership preservation forces x and "
                        + "y to be empty, and both families have empty index type. Empty "
                        + "columns and row factors, empty or infinite alphabets, and "
                        + "repeated letters are included. Irreflexivity forbids a letter "
                        + "from occurring in an earlier lower and a later upper factor "
                        + "simultaneously. No decidable equality, finite or nonempty "
                        + "alphabet, occurrence matching, partial order, swap schedule, "
                        + "or refinement is an input.")),
                    Paragraph(Text("Cori and Perrin's Corollary 1.4 on printed pages "
                        + "25–26 gives the classical finite-product refinement under "
                        + "their standing assumptions of a finite alphabet A and "
                        + "reflexive symmetric commutation theta. Their u,v,x_i,p_i,q_i "
                        + "correspond to x,y,zs[i],p(i),r(i). Their literal column "
                        + "factorizations imply column congruences, and symmetry "
                        + "aligns their earlier-bottom/later-top direction with the "
                        + "displayed I(a,b). The convention theta(a,b) := a=b or I(a,b) "
                        + "alone does not give strict independence. The native result "
                        + "uses the strict binary Levi theorem for arbitrary alpha. "
                        + "The citation supplies the classical analogue; no novelty, "
                        + "effective reconstruction, or complexity bound is asserted."))),
                DescribeRole.Theorem))));

    private static Formula MultiCutStatement()
    {
        var alphabet = V("alpha");
        var word = Call("List", alphabet);
        var indices = Call("Fin", Call("length", V("zs")));
        var family = new Formula.TypeArrow(indices, word);
        var letters = All("a", alphabet,
            Implication(Call("Mem", V("a"), Call("p", V("k"))),
                All("b", alphabet,
                    Implication(Call("Mem", V("b"), Call("r", V("j"))),
                        Call("I", V("a"), V("b"))))));
        var crossing = All("j", indices, All("k", indices,
            Implication(Call("lt", V("j"), V("k")), letters)));
        Formula factors = Q(
            Call("Connected", V("I"), V("x"), Call("flatten", Call("ofFn", V("p")))), Land,
            Call("Connected", V("I"), V("y"), Call("flatten", Call("ofFn", V("r")))), Land,
            Seq(Open, All("j", indices,
                Call("Connected", V("I"), Call("column", V("zs"), V("j")),
                    Call("append", Call("p", V("j")), Call("r", V("j"))))), Close), Land,
            Seq(Open, crossing, Close));
        foreach (var name in new[] { "r", "p" })
            factors = new Formula.Bind(FormulaQuantifier.Exists,
                FormulaIdentifier.Create(name), family, factors);
        Formula result = Q(
            Call("Connected", V("I"), Call("append", V("x"), V("y")), Call("flatten", V("zs"))),
            Iff, Seq(Open, factors, Close));
        result = All("zs", Call("List", word), result);
        foreach (var name in new[] { "y", "x" })
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
        Q(Seq(Open, premise, Close), Implies, Seq(Open, conclusion, Close));
    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[2 * items.Length - 1];
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
