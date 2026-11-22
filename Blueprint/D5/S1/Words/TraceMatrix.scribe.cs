using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class TraceMatrixDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/coriperrin1985traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single matrix simultaneously refines every row and column of two finite trace products.",
        H("Common Refinement Matrices for Native Traces"),
        Blocks(
            Paragraph(Text("Fix a universe level u as a universe metaparameter, an alphabet "
                + "alpha in Type(u), and a symmetric irreflexive relation I. Words are native "
                + "finite List(alpha) values. Connected denotes precisely "
                + "D5.S1.Words.TraceProjection.Connected: the reflexive transitive closure "
                + "of exchanging adjacent letters a,b satisfying I(a,b), inside arbitrary "
                + "unchanged left and right contexts. The operations length, entry, Mem, "
                + "ofFn and flatten are native list length, list indexing, membership, "
                + "increasing Fin-indexed enumeration and ordered concatenation. Thus "
                + "entry(xs,i) means xs[i], and Fin(length(xs)) includes exactly the row "
                + "indices. The two arguments of w are respectively a row and a column.")),
            Describe.Lean(
                DescribeId.Create("trace-matrix-connected-flatten"),
                DeclarationHandle.Create("D5/S1/Words/TraceMatrix.connected_flatten_iff"),
                H("One simultaneous matrix with strict crossings"),
                StatementSource.FromAuthor(MatrixStatement()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For arbitrary finite lists of words xs and ys, their "
                        + "concatenations are connected exactly when there is one matrix "
                        + "w of words on Fin(length(xs)) by Fin(length(ys)). Each original "
                        + "row xs[i] is connected to its matrix row, read from left to "
                        + "right, and each original column ys[j] is connected to its "
                        + "matrix column, read from top to bottom. If i < ii and jj < j, "
                        + "every a in w(i,j) and every b in w(ii,jj) satisfy I(a,b). The "
                        + "same w occurs in all row, column and crossing conditions.")),
                    Paragraph(Text("Induct on the rows. Separate the first word x from "
                        + "the concatenation of the remaining rows. The two-row result "
                        + "D5.S1.Words.TraceMultiCut.connected_append_flatten_iff gives "
                        + "one upper family p and one lower family r, with each ys[j] "
                        + "connected to p(j) ++ r(j). Apply the induction hypothesis to "
                        + "the remaining rows and the ordered family r, producing a "
                        + "single matrix v. Prepending p to v gives w. Its lower rows "
                        + "and their mutual crossings come from induction. Its column "
                        + "connections compose the two-row column connections with "
                        + "the corresponding column connections of v.")),
                    Paragraph(Text("For a crossing involving the first row, a letter b "
                        + "in v(i,jj) belongs to the concatenation of column jj of v. "
                        + "D5.S1.Words.TraceLevi.mem_of_connected transports that "
                        + "membership back to r(jj). The two-row strict crossing law "
                        + "then gives I(a,b) for every a in p(j) when jj < j. This "
                        + "transfers the whole lower-column constraint to each of its "
                        + "individual factors while preserving a common choice.")),
                    Paragraph(Text("Conversely, remove the first row of a given matrix "
                        + "and concatenate each remaining column to form r(j). The "
                        + "induction hypothesis connects the remaining source rows "
                        + "to the product of these r(j). Every letter in r(jj) occurs "
                        + "in some lower cell, so the prescribed matrix crossings "
                        + "give the two-row crossings. Applying the same two-row "
                        + "equivalence reconstructs the original connection.")),
                    Paragraph(Text("With zero rows, membership preservation forces "
                        + "every column word to be empty; the matrix has empty row "
                        + "index type. Zero columns are included by the two-row "
                        + "equivalence and the induction. Empty individual factors, "
                        + "repeated letters, and empty or infinite alphabets are all "
                        + "included. No decidable equality, nonempty alphabet, nonzero "
                        + "dimension, occurrence matching, order representation, swap "
                        + "schedule, or prior refinement is assumed.")),
                    Paragraph(Text("Cori and Perrin's Proposition 1.3 and Corollary 1.4 "
                        + "on printed pages 25–26 give the classical binary and two-row "
                        + "analogues for finite alphabets with reflexive symmetric "
                        + "commutation theta. Their two upper and lower factor "
                        + "families correspond to p and r in the induction. The "
                        + "arbitrary-row matrix follows here by the additional row "
                        + "induction using the native strict two-row result. The "
                        + "substitution theta(a,b) := a=b or I(a,b) alone does not "
                        + "imply strict I(a,b), and the cited source does not state "
                        + "this arbitrary-universe native matrix formula verbatim. "
                        + "No originality, published open-problem resolution, "
                        + "effective reconstruction or complexity bound is asserted."))),
                DescribeRole.Theorem))));

    private static Formula MatrixStatement()
    {
        var alphabet = V("alpha");
        var word = Call("List", alphabet);
        var rows = Call("Fin", Call("length", V("xs")));
        var columns = Call("Fin", Call("length", V("ys")));
        var matrix = new Formula.TypeArrow(rows, new Formula.TypeArrow(columns, word));
        var row = All("i", rows,
            Call("Connected", V("I"), Call("entry", V("xs"), V("i")),
                Call("flatten", Call("ofFn", Call("w", V("i"))))));
        var column = All("j", columns,
            Call("Connected", V("I"), Call("entry", V("ys"), V("j")),
                Call("flatten", Call("ofFn",
                    Lambda("i", rows, Call("w", V("i"), V("j")))))));
        var letters = All("a", alphabet,
            Implication(Call("Mem", V("a"), Call("w", V("i"), V("j"))),
                All("b", alphabet,
                    Implication(Call("Mem", V("b"), Call("w", V("ii"), V("jj"))),
                        Call("I", V("a"), V("b"))))));
        var crossings = All("i", rows, All("ii", rows,
            All("j", columns, All("jj", columns,
                Implication(Call("lt", V("i"), V("ii")),
                    Implication(Call("lt", V("jj"), V("j")), letters))))));
        Formula conditions = Q(Seq(Open, row, Close), Land,
            Seq(Open, column, Close), Land, Seq(Open, crossings, Close));
        var factors = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("w"), matrix, conditions);
        Formula result = Q(Call("Connected", V("I"), Call("flatten", V("xs")),
            Call("flatten", V("ys"))), Iff, Seq(Open, factors, Close));
        foreach (var name in new[] { "ys", "xs" })
            result = All(name, Call("List", word), result);
        var symmetry = All("a", alphabet, All("b", alphabet,
            Implication(Call("I", V("a"), V("b")), Call("I", V("b"), V("a")))));
        var irreflexivity = All("a", alphabet, new Formula.Not(Call("I", V("a"), V("a"))));
        return Disp(All("alpha", Call("Type", V("u")),
            All("I", new Formula.TypeArrow(alphabet, new Formula.TypeArrow(alphabet, V("Prop"))),
                Implication(symmetry, Implication(irreflexivity, result)))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Q(Open, V(name), Colon, domain, Mapsto, body, Close);
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
