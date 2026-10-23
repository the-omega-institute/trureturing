using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class DimerVirialFourthDifferenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/DimerVirialFourthDifferenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/butera2015virial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Butera, Federbush and Pernici (arXiv:1502.06734) ask whether the bounds Delta^k ln(i! N(i)) <= 0 for k <= 4 always hold for regular biconnected graphs, where N(i) counts the configurations of i dimers. They do not: a 6-regular biconnected graph on 28 vertices, made of four copies of K_7 minus an edge joined in a ring, has a positive fourth difference at i = 10.",
        H("A regular biconnected graph with a positive fourth difference of ln(i! N(i))"),
        Blocks(
            Node("aey-owner-edgedisjoint", "Two edges share no vertex", Disp(Seq(Forall, Sp, Seq(Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, F.Id("Type"))), Parenthesized(Seq(F.Id("e"), Sp, F.Id("f"), Sp, Colon, Sp, F.Id("Sym2"), Sp, F.Id("V")))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("EdgeDisjoint"), Sp, F.Id("e"), Sp, F.Id("f"))), Iff, Parenthesized(Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, F.Id("V"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("v"), Sp, InMacro, Sp, F.Id("e"))), To, Parenthesized(Seq(Neg, Sp, Parenthesized(Seq(F.Id("v"), Sp, InMacro, Sp, F.Id("f")))))))))))),
                "Two unordered edges are disjoint when every endpoint of the first is absent from the second.", "EdgeDisjoint", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("aey-owner-matchingsin", "Finite matchings within an edge set", Disp(Seq(Forall, Sp, Seq(Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, F.Id("Type"))), Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("V")), CloseBracket), Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("V")), CloseBracket), Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Sym2"), Sp, F.Id("V"))))), Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))))), Comma, Sp, Seq(F.Id("matchingsIn"), Sp, F.Id("E"), Sp, F.Id("i"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("E"), Sp, Dot, Sp, F.Id("powersetCard"), Sp, F.Id("i"))), Dot, Sp, F.Id("filter"), Sp, Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Sym2"), Sp, F.Id("V"))))), Mapsto, Sp, Forall, Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, F.Id("Sym2"), Sp, F.Id("V"))), Comma, Sp, F.Id("e"), Sp, InMacro, Sp, F.Id("S"), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, F.Id("Sym2"), Sp, F.Id("V"))), Comma, Sp, F.Id("f"), Sp, InMacro, Sp, F.Id("S"), Sp, To, Sp, F.Id("e"), Sp, Neq, Sp, F.Id("f"), Sp, To, Sp, F.Id("EdgeDisjoint"), Sp, F.Id("e"), Sp, F.Id("f")))))),
                "The finite collection consists of all i-element edge subsets whose distinct members have disjoint endpoints.", "matchingsIn", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("aey-owner-cnt", "The cardinality of the finite matching family", Disp(Seq(Forall, Sp, Seq(Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, F.Id("Type"))), Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("V")), CloseBracket), Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("V")), CloseBracket), Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Sym2"), Sp, F.Id("V"))))), Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))))), Comma, Sp, Seq(F.Id("cnt"), Sp, F.Id("E"), Sp, F.Id("i"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("matchingsIn"), Sp, F.Id("E"), Sp, F.Id("i"))), Dot, Sp, F.Id("card")))),
                "The sequence counts the finite matching families of each size.", "cnt", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("aey-owner-matchingsin-eq-empty", "Too few vertices for a matching", Disp(Seq(Forall, Sp, Seq(Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, F.Id("Type"))), Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("V")), CloseBracket), Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("V")), CloseBracket), Parenthesized(Seq(F.Id("E"), Sp, Colon, Sp, F.Id("Finset"), Sp, Parenthesized(Seq(F.Id("Sym2"), Sp, F.Id("V"))))), Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, F.Id("Finset"), Sp, F.Id("V")))), Comma, Sp, Seq(Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, F.Id("Sym2"), Sp, F.Id("V"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("e"), Sp, InMacro, Sp, F.Id("E"))), To, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, F.Id("V"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("v"), Sp, InMacro, Sp, F.Id("e"))), To, Parenthesized(Seq(F.Id("v"), Sp, InMacro, Sp, F.Id("s"))))))))), To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, F.Id("Sym2"), Sp, F.Id("V"))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("e"), Sp, InMacro, Sp, F.Id("E"))), To, Parenthesized(Seq(Neg, Sp, F.Id("e"), Sp, Dot, Sp, F.Id("IsDiag")))))), To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, F.Id("s"), Sp, Dot, Sp, F.Id("card"), Sp, Lt, Sp, D(2), Sp, Cdot, Sp, F.Id("i"), Sp, To, Sp, F.Id("matchingsIn"), Sp, F.Id("E"), Sp, F.Id("i"), Sp, Eq, Sp, Emptyset))),
                "An i-edge matching of loop-free edges covers 2i distinct vertices. Consequently no such matching fits inside a vertex set of cardinality less than 2i.", "matchingsIn_eq_empty", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("count", "Dimer configurations", CountFormula(),
                "N(i) is the number of configurations of i dimers on G, that is, of sets of i pairwise vertex-disjoint edges of G. Here Matching(n, i) is the set of sets of i unordered, loop-free, pairwise vertex-disjoint pairs of vertices of Fin(n), and N(G, i) is the number of its elements all of whose pairs are edges of G.",
                "matchingCount", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nu", "The matching number", NuFormula(),
                "The matching number nu(G) is the maximum number of pairwise disjoint edges of G; it is the supremum of the i with N(G, i) > 0.",
                "matchingNumber", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("biconnected", "Biconnected graphs", BiconnectedFormula(),
                "A graph is biconnected when it is connected and remains connected after deleting any one vertex: the subgraph induced on the complement of {v} is connected for every vertex v.",
                "Biconnected", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The question for k at most 4", ClaimFormula(),
                "The paper's Eq. (1) is Delta^k ln(i! N(i)) <= 0 for k = 2, ..., nu and i = 0, ..., nu - k, with Delta the forward difference in i, and its Section IV B asks whether these bounds for k <= 4 are always satisfied for regular biconnected graphs. The displayed statement reads the question as a universal statement over finite simple graphs on Fin(n): regularity is the existence of a common degree d, and Delta^k is the k-th iterate of the forward difference with step 1. For k = 2 the bound follows from the Heilmann-Lieb inequality.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The answer is negative", Disp(new Formula.Not(ClaimBody())),
                "Take the graph on the 28 vertices x = 7b + t, with block b in {0, 1, 2, 3} and position t in {0, ..., 6}: inside a block all pairs of vertices are adjacent except positions 0 and 1, and position 1 of block b is adjacent to position 0 of block b + 1 modulo 4. Every vertex has degree 6. Visiting positions 0, 2, 3, 4, 5, 6, 1 of blocks 0, 1, 2, 3 in turn is a Hamiltonian cycle, and deleting one vertex from it leaves a Hamiltonian path of the other vertices, so the graph is biconnected. For an edge e of an edge set E, the (i + 1)-matchings of E either avoid e or contain it, so N(E, i + 1) = N(E - e, i + 1) + N(E_e, i), where E_e is the set of edges of E disjoint from e; for two edge sets without a common vertex the matching sequence of the union is the Cauchy product of the two sequences. The first rule applied to the four connecting edges and the second to the four blocks reduce the count to the matching sequences of K_7 minus an edge, K_6 and K_5, which are (1, 20, 95, 90), (1, 15, 45, 15) and (1, 10, 15). This gives N(10) = 845745750, N(11) = 506745000, N(12) = 141530625, N(13) = 9922500 and N(14) = 101250, and nu = 14 because 28 vertices carry at most 14 disjoint edges. With A_i = i! N(i), the fourth difference of ln A at i = 10 is ln(A_10 A_12^6 A_14) - ln(A_11^4 A_13^4), which is positive because A_11^4 A_13^4 < A_10 A_12^6 A_14 as integers. So k = 4 and i = 10, with i + k = nu, violate the bound.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("butera-2015-dimer-virial-bounds-regular-biconnected"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("dvf-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula NumberSet(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula GraphType(Formula n) => Call("SimpleGraph", Call("Fin", n));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula SetOfWhere(Formula element, Formula binder, Formula domain, Formula condition) =>
        Seq(Esc, OpenBrace, element, Sp, Mid, Sp, Member(binder, domain), Comma, Sp, condition,
            Esc, CloseBrace);
    private static Formula Singleton(Formula x) => Seq(Esc, OpenBrace, x, Esc, CloseBrace);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Count(Formula g, Formula i) => Call("matchingCount", g, i);

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), i = F.Id("i"), m = F.Id("M");
        Formula inside = Rel(m, FormulaRelationOperator.SubsetOf, Call("edgeSet", g));
        Formula set = SetOfWhere(m, m, Call("Matching", n, i), inside);
        return Disp(All(n, NumberSet("N"), All(g, GraphType(n), All(i, NumberSet("N"),
            EqTo(Count(g, i), Call("card", set))))));
    }

    private static Formula NuFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), i = F.Id("i");
        Formula positive = Rel(D(0), FormulaRelationOperator.LessThan, Count(g, i));
        return Disp(All(n, NumberSet("N"), All(g, GraphType(n),
            EqTo(Call("matchingNumber", g), Call("sSup", SetOfWhere(i, i, NumberSet("N"), positive))))));
    }

    private static Formula BiconnectedFormula()
    {
        Formula g = F.Id("G"), v = F.Id("v"), vertices = F.Id("V");
        Formula deleted = Call("Connected", Call("induce", Call("compl", Singleton(v)), g));
        return Disp(All(vertices, Named("Type"), All(g, Call("SimpleGraph", vertices),
            Logic(Call("Biconnected", g), FormulaLogicOperator.Iff,
                Logic(Call("Connected", g), FormulaLogicOperator.And, All(v, vertices, deleted))))));
    }

    private static Formula ClaimFormula() =>
        Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), g = F.Id("G"), d = F.Id("d"), k = F.Id("k"), i = F.Id("i"),
            j = F.Id("j");
        Formula logTerm = Call("log", Mul(Seq(j, Bang), Count(g, j)));
        Formula sequence = Parenthesized(Seq(j, Mapsto, logTerm));
        Formula difference = new Formula.Apply(
            Parenthesized(Seq(new Formula.Power(Delta, k), Sp, sequence)), [i]);
        Formula bound = Rel(difference, FormulaRelationOperator.LessThanOrEqual, D(0));
        Formula range = Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, k),
            Imp(Rel(k, FormulaRelationOperator.LessThanOrEqual, D(4)),
                Imp(Rel(Add(i, k), FormulaRelationOperator.LessThanOrEqual,
                    Call("matchingNumber", g)), bound)));
        Formula regular = Some(d, NumberSet("N"), Call("IsRegularOfDegree", g, d));
        Formula body = Imp(regular, Imp(Call("Biconnected", g),
            All(k, NumberSet("N"), All(i, NumberSet("N"), range))));
        return All(n, NumberSet("N"), All(g, GraphType(n), body));
    }
}
