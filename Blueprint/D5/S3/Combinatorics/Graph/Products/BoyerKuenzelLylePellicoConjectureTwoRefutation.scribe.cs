using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class BoyerKuenzelLylePellicoConjectureTwoRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/" +
        "BoyerKuenzelLylePellicoConjectureTwoRefutation.";
    private static readonly LibraryNoteRef Primary =
        LibraryNoteRef.Create("D5/L/GraphInvariants/boyerkuenzellylepellico2025wellhued");
    private static readonly LibraryNoteRef Supplier =
        LibraryNoteRef.Create("D5/L/GraphInvariants/goddardkuenzelmelville2022wellhued");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite-graph Conjecture 2 of Boyer--Kuenzel--Lyle--Pellico is false.",
        H("Refuting the unrestricted Conjecture 2"), Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 2 in its complete quantified form"),
                StatementSource.FromAuthor(Disp(Iff(C("claim"), WholeClaim()))),
                AssessedProvenance.FromLiterature(Primary),
                Blocks(Paragraph(Text(
                    "Boyer, Kuenzel, Lyle and Pellico state Conjecture 2 in Section 3, printed page 10, " +
                    "of arXiv:2506.04993v1. Although the surrounding section studies independence " +
                    "number two, this conjecture explicitly replaces two by alpha(G). The definition " +
                    "therefore retains every finite simple graph and every positive integer k; " +
                    "Theorem 4 of that paper is a separate restricted statement.")),
                    Paragraph(Text(
                    "ProperColorable G j S means that a map from the vertex type to Fin j is proper " +
                    "on the induced set S. Each set and each extension may choose a fresh coloring. " +
                    "For positive j, extending a coloring outside S is unrestricted. MaximalColorable " +
                    "requires this property on S and its failure on every one-vertex extension. " +
                    "By heredity this is inclusion-maximal induced colorability, allowing recoloring. " +
                    "WellHued requires equal orders for every pair of such sets for every positive j. " +
                    "HasSequence specifies order j times the independence number for 1 <= j <= k. " +
                    "HasChromaticNumber requires a k-coloring and excludes every smaller number of colors.")),
                    Paragraph(Text(
                    "The left side is connectedness together with these three properties. " +
                    "BalancedMultipartiteSubgraph means that k pairwise disjoint independent parts, " +
                    "each of size alpha(G), cover the vertex set. This is exactly a spanning subgraph " +
                    "of the balanced complete k-partite host. AntiNeighborhoodFree excludes an " +
                    "independent set of size alpha(G) outside each closed neighborhood: the forbidden " +
                    "induced graph in the source is the edgeless graph, with the overline retained. " +
                    "These two conditions form the right side."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The 3 by 3 rook graph counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(WholeClaim()))),
                AssessedProvenance.FromRepo(Primary, Supplier),
                Blocks(Paragraph(Text(
                    "The graph on Fin 3 times Fin 3 joins distinct cells in a common row or column. " +
                    "Its independence number is three: the diagonal is independent and an independent " +
                    "set has at most one cell in each row. The three parts given by row plus column " +
                    "modulo three are independent triples, disjoint and covering the board. " +
                    "An independent triple outside a closed neighborhood could be enlarged by its " +
                    "center, contradicting the independence number. Thus the right side holds at k=3.")),
                    Paragraph(Text(
                    "The set S={(0,0),(0,1),(1,0),(1,1),(2,2)} induces a four-cycle and an isolated " +
                    "vertex. The set T={(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)} induces a six-cycle. " +
                    "The proof checks proper two-colorability and failure of two-colorability for " +
                    "every one-vertex extension of each set, under any recoloring. Their unequal " +
                    "orders five and six contradict WellHued. Applying the conjectured reverse " +
                    "implication to this graph therefore refutes the entire quantified equivalence.")),
                    Paragraph(Text(
                    "The rook-graph classification and its failure of well-huedness are due to " +
                    "Goddard, Kuenzel and Melville, Well-hued graphs (2022), Lemma 6 and Theorem 10. " +
                    "Their criterion says that K_m box K_n, for n >= m, is well-hued exactly when " +
                    "n >= 2(m-1); their maximal-colorability construction supplies the obstruction " +
                    "used here at m=n=3. These facts are credited to that source. The conclusion here " +
                    "connects this obstruction to the unrestricted Conjecture 2 of the 2025 paper. " +
                    "It establishes no corrected conjecture and makes no priority claim."))),
                DescribeRole.Theorem)), []));

    private static Formula WholeClaim()
    {
        var v = F.Id("V");
        var g = F.Id("G");
        var k = F.Id("k");
        var left = And(C("Connected", g), And(C("WellHued", g),
            And(C("HasSequence", g, k), C("HasChromaticNumber", g, k))));
        var right = And(C("BalancedMultipartiteSubgraph", g, k), C("AntiNeighborhoodFree", g));
        return All("V", C("Type"),
            Seq(OpenBracket, C("Fintype", v), CloseBracket, Sp,
                OpenBracket, C("DecidableEq", v), CloseBracket, Sp,
                All("G", C("SimpleGraph", v), All("k", C("Nat"),
                    Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, k),
                        Iff(left, right))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula C(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
