using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MinusFourReplicationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MinusFourReplication.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hub and pendant choices give an exact generating evaluation for every finite graph and every copy count. Throughout, V is an arbitrary finite vertex type supplied with Fintype and DecidableEq instances.",
        H("Weighted ordinary domination under hub replication"),
        Blocks(
            Node("evaluation", "Cardinality-weighted ordinary domination", "evaluation", DescribeRole.Definition,
                "For a finite simple graph H and integer x, evaluation(H,x) is the sum of x raised to the cardinality of S over the existing finite family domSets(H). Ordinary domination means that every vertex is selected or has a selected neighbor. The selected subset itself need not be connected."),
            Node("replicated-evaluation", "The complete two-case weighted identity", "replicated_evaluation", DescribeRole.Theorem,
                "For every finite vertex type V, graph H, attachment set U, nonnegative copy count r and integer x, evaluation(replicated(H,U,r),x) equals x(1+x) times the r-th power of the weighted partial-family sum, plus x times evaluation(H,x) to the r-th power. The existing hubEquiv parametrizes the hub-containing sets by a pendant bit and one partial set per copy. The existing omittedEquiv parametrizes the other sets by one full dominating set per copy. These are disjoint exhaustive cases. In each inverse map, assemble_card adds the copy cardinalities and the two bits. Powers therefore multiply, and Fintype.sum_pow sums independent choices. This uses the actual configuration equivalences; a formula about average cardinalities alone would not suffice."),
            Node("support-evaluation", "An actual internal leaf closes the partial family", "support_replication_evaluation", DescribeRole.Theorem,
                "Suppose w is a degree-one vertex of H adjacent to v. A set dominating outside the singleton v must dominate w. The existing leaf_dominated_iff forces w or v to be selected, so v is internally dominated too. Thus partialSets(H,{v}) equals domSets(H), and the weighted identity becomes x(x+2) times evaluation(H,x) to the r-th power. This statement holds also at r=0, when the construction consists of the hub and pendant."),
            Node("support-connected", "Paths through each copy support", "support_replication_connected", DescribeRole.Theorem,
                "For any connected H, support v and nonnegative r, the replicated graph is connected. A copied vertex has an H-path to its own copy of v. That copy has an edge to the hub, and the pendant has its hub edge. Mapping the H-path through the copy embedding gives actual reachability. For zero copies the hub and pendant still form one connected edge."),
            Paragraph(Text("At x equal to minus four the support identity is eight times the r-th power of the base evaluation. A zero base value gives zero whenever r is positive. For r=0 the value is eight, so positivity of the copy count is essential to a root-family application. The weighted factorization is a repository derivation from existing finite-family interfaces; it carries no claim of literature priority."))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            Statement(declaration), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static StatementSource Statement(string declaration)
    {
        if (declaration == "evaluation") return StatementSource.WithoutFormula();
        var h = Id("H"); var v = Id("v"); var w = Id("w"); var r = Id("r"); var x = Id("x");
        Formula rhs; Formula body;
        var lhs = Call("evaluation", Call("replicated", h, Id("U"), r), x);
        if (declaration == "replicated_evaluation")
        {
            var sum = Seq(new Formula.Subscript(Sum,
                Seq(Id("S"), InMacro, Call("partialSets", h, Id("U")))), Sp,
                new Formula.Power(x, Call("card", Id("S"))));
            rhs = Add(Mul(Mul(x, P(Add(D(1), x))), new Formula.Power(P(sum), r)),
                Mul(x, new Formula.Power(Call("evaluation", h, x), r)));
            body = All("U", Call("Finset", Id("V")), All("r", Nat, All("x", Integer, Eq(lhs, rhs))));
        }
        else
        {
            var singleton = Seq(new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), v,
                new Formula.LatexMacro(FormulaLatexMacro.CloseBrace));
            var replicated = Call("replicated", h, singleton, r);
            if (declaration == "support_replication_connected")
                body = All("v", Id("V"), All("r", Nat,
                    ImpliesF(Call("Connected", h), Call("Connected", replicated))));
            else
            {
                rhs = Mul(Mul(x, P(Add(x, D(2)))), new Formula.Power(Call("evaluation", h, x), r));
                body = All("v", Id("V"), All("w", Id("V"),
                    ImpliesF(And(Call("Leaf", h, w), Call("Adj", h, w, v)),
                        All("r", Nat, All("x", Integer, Eq(Call("evaluation", replicated, x), rhs))))));
            }
        }
        return StatementSource.FromAuthor(Disp(All("H", Call("SimpleGraph", Id("V")), body)));
    }
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Integer => Seq(Mathbb, Grp(Id("Z")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula ImpliesF(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
}
