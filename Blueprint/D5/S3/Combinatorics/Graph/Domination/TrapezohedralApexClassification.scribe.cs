using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralApexClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralApexClassification.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every connected minimal dominating subset has exactly one apex and one selected opposite rim label.",
        H("Classification by an apex and an opposite label"),
        Blocks(
            Paragraph(Text("All statements concern the original graph on alpha, beta, a(i), b(i), and actual selected vertex subsets. Closed domination and minimality among all proper subsets are unchanged. If both apices are selected, minimality forces the disconnected apex pair. If neither is selected, domination of each apex supplies selected labels of both types. A unique selected label of either type would force all labels of the other type into two neighbors, contradicting n>=3. Closed-private witnesses then force each selected b-vertex to have at most one selected a-neighbor. Connectivity propagates the same a-label along every selected walk, contradicting the existence of two selected a-labels. This avoids any finite-size extrapolation.")),
            Node("one-apex", "Exactly one apex", "exactly_one_apex",
                "For every n>=3 and every admissible original subset S, exactly one of alpha and beta belongs to S."),
            Node("alpha-opposite", "The alpha branch", "alpha_unique_opposite",
                "If alpha belongs to S and beta does not, exactly one b-label is selected. Connectivity prevents a selected b-vertex from using itself privately; alpha prevents either neighboring a-label from witnessing it privately. Its private witness is therefore beta, which forces uniqueness."),
            Node("reconstruction", "Read and reconstruct", "alpha_reconstruction",
                "In the alpha branch the unique selected b-label j and the membership of the selected a-labels reconstruct the entire original subset. Different j cannot reconstruct the same subset. No quotient by graph symmetries is taken.")), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(Presentation(declaration))), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Presentation(string name)
    {
        Formula n = V("n"), set = V("S"), j = V("j"), k = V("k"), i = V("i");
        Formula fin = Call("Fin", n), vertex = Call("Vertex", n);
        Formula ha = Mem(Call("alpha"), set), hb = Mem(Call("beta"), set);
        Formula Body(Formula body) => All("n", Nat, All("S", Call("Set", vertex), Imp(Call("Admissible", set), body)));
        Formula Unique(Formula predicate, Formula same) => Some("j", fin, And(predicate, All("k", fin, Imp(same, Eq(k, j)))));
        if (name == "exactly_one_apex") return All("n", Nat, Imp(Le(D(3), n), All("S", Call("Set", vertex),
            Imp(Call("Admissible", set), Or(And(ha, new Formula.Not(hb)), And(hb, new Formula.Not(ha)))))));
        Formula result = name == "alpha_unique_opposite"
            ? Unique(Mem(Call("b", j), set), Mem(Call("b", k), set))
            : Unique(Eq(set, Call("alphaSet", j, SetOf("i", fin, Mem(Call("a", i), set)))),
                Eq(set, Call("alphaSet", k, SetOf("i", fin, Mem(Call("a", i), set)))));
        return Body(Imp(ha, Imp(new Formula.Not(hb), result)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula SetOf(string name, Formula type, Formula body) => Seq(OpenBrace, V(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
