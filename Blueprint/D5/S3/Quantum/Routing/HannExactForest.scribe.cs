using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannExactForestDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannExactForest.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual signed loaded-record relation has the prescribed fixed-coordinate forest lift at every height.",
        H("Exact signed node lift"),
        Blocks(
            Def("forest-nodes", "Node", "Original words and independent coordinates",
                "Node 0 is Unit; Node(n+1) is Option(Bool times Node n). The root is Unit at zero "
                + "and none at positive height. some(b,v) prepends the literal first bit. Thus Node n "
                + "indexes all words of length at most n. Address n remains the original head-first "
                + "address type, and Router n indexes words of length strictly less than n. "
                + "Variable n is Address n disjoint-union Node n: even at height zero the address "
                + "and the leaf/root are different coordinates. Every address is retained, regardless "
                + "of coincidences between records. No columns are rescaled or repeated."),
            Def("forest-equations", "Equations", "All node clauses",
                "At height zero impose c(root)-x(empty)=0. At positive height impose Local at the "
                + "root and recurse in each child using childCoeff n x b and childValues n c b. "
                + "The child's rate is exactly HannSignedCertificate.restrict n q b; every descendant "
                + "therefore uses the restriction of the same heterogeneous q. Local(t,z,l,r) is "
                + "z-l-r=0 at t=1, the two equations l+z=0 and r+z=0 at t=-1/2, and the three "
                + "equations z=0,l=0,r=0 elsewhere. The rate hypothesis puts this last case strictly "
                + "between the endpoints. There is no additional root equation."),
            Def("forest-rows", "Row", "Distinct node and clause identities",
                "Clause t uses labels in Fin 3: only label 0 at t=1; labels 0 and 1 at t=-1/2; "
                + "all three labels otherwise. Row 0 q is Unit. Row(n+1,q) is the disjoint union "
                + "of root clauses and the sigma type of a child bit and one of that child's rows. "
                + "Rows with identical numerical coefficients remain distinct vertices."),
            Def("forest-matrix", "matrix", "The literal real homogeneous matrix",
                "The leaf row has coefficient -1 on its original address and +1 on its leaf node. "
                + "An upper root row has +1 at the root and -1 at each child root. A lower root "
                + "row with label 0 has +1 at the root and left child; label 1 has +1 at the root "
                + "and right child. In the remaining case labels 0,1,2 select respectively the "
                + "root,left child,right child, with coefficient +1. All other root-row entries "
                + "are zero. Child rows insert their exact child matrix with zeros outside that "
                + "child's address and node coordinates. complexMatrix casts these real entries "
                + "entrywise to Complex. coordinates n x c is the disjoint-union vector (x,c)."),
            Def("forest-projection", "Projected", "Forget only nonroot node variables",
                "Projected n q x z means there is a node assignment c with c(root)=z satisfying "
                + "all Equations. Every x coordinate survives the projection. The matrix theorem "
                + "identifies these equations with complexMatrix.mulVec(coordinates x c)=0, "
                + "equivalently membership in the complex linear kernel. The actual source synthesis "
                + "is the sum of x(a) record(n,q,bus,a), and vacuumRecord is the source vacuum tensor."),
            Describe.Lean(DescribeId.Create("actual-relation-exact-matrix-kernel"),
                DeclarationHandle.Create(Module + "relation_iff_matrix_kernel"),
                H("Bidirectional actual-record relation"),
                StatementSource.FromAuthor(RelationStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both directions hold for every height including zero, every q in the closed "
                    + "signed interval, every qutrit bus, and all complex x and z. The forward "
                    + "construction uses the original upper_relation and below_upper_relation "
                    + "suppliers and recursively assembles one global node assignment. The reverse "
                    + "direction uses the original synthesis_split, vacuum_split, local_upper and "
                    + "local_lower suppliers and the actual child equations. No child realization "
                    + "is chosen independently. At height zero the source record and vacuum are one, "
                    + "and the one row equates the distinct x and c coordinates.")))),
            Describe.Lean(DescribeId.Create("literal-matrix-support-forest"),
                DeclarationHandle.Create(Module + "support_is_acyclic"),
                H("Exact row-variable support is a forest"),
                StatementSource.FromAuthor(ForestStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "support has one vertex for each Row and one for each Variable, with an edge "
                    + "exactly when the real matrix entry is nonzero. The assertion holds even "
                    + "without the rate-interval hypothesis. Give addresses rank zero, a node of "
                    + "remaining height h rank 3h+2, and a row owned by that node rank 3h+1. Each "
                    + "row has at most one later variable; each variable has at most one later "
                    + "row. The existing chronological pruning supplier then excludes cycles. "
                    + "Separate unary rows and both lower-endpoint rows are included in this argument.")))),
            Paragraph(Text(
                "This is a repository-derived exact relation and support theorem. It asserts no "
                + "equal-weight or nonnegative certificate, probability-normalized total unimodularity, "
                + "minimum, U0/U1 conclusion, physical signed continuation, Schur or Choi statement, "
                + "resource bound, hardware claim, or claim of originality.")))));

    private static DocumentBlock Def(string id, string symbol, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + symbol), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula RelationStatement()
    {
        Formula n=I("n"), q=I("q"), bus=I("bus"), x=I("x"), z=I("z"), c=I("c"), v=I("v");
        Formula routers=C("Router",n), coeff=Arr(C("Address",n),I("Complex"));
        Formula rates=All("v",routers,And(Le(C("neg",new Formula.Fraction(D(1),D(2))),App(q,v)),
            Le(App(q,v),D(1))));
        Formula relation=Eq(App(C("synthesis",n,q,bus),x),C("smul",z,C("vacuumRecord",n,q)));
        Formula lift=Ex("c",Arr(C("Node",n),I("Complex")),And(Eq(App(c,C("root",n)),z),
            Eq(C("mulVec",C("complexMatrix",n,q),C("coordinates",n,x,c)),D(0))));
        return All("n",I("Nat"),All("q",Arr(routers,I("Real")),All("bus",I("Qutrit"),
            Imp(rates,All("x",coeff,All("z",I("Complex"),IffOf(relation,lift)))))));
    }

    private static Formula ForestStatement() => All("n",I("Nat"),
        All("q",Arr(C("Router",I("n")),I("Real")),C("IsAcyclic",C("support",I("n"),I("q")))));
}
