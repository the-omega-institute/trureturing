using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class IntegerLatticeFiniteMotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeFiniteMotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite occupied configurations on the infinite integer lattice, with one common infinite legal covering trajectory after scaling by four.",
        H("Finite configurations and infinite mobility"),
        Blocks(
            Paragraph(Text("The signed-unit lattice has vertices Fin k to Int. Its edges change exactly one coordinate by one in either direction. General position and legal moves use CylinderSevenTen.IsGeneralPosition and CylinderSevenTen.LegalMove in this actual graph.")),
            Node("infinite-mobility", "One common infinite trajectory", "IsInfinitelyMobile",
                DescribeRole.Definition, MobilityFormula(),
                "A finite configuration is initially in graph general position. There is one function c from natural times to finite configurations, starting at that configuration, with a legal move at every step. Every c(t) is in graph general position, every vertex belongs to some c(t) at a finite time, and every c(t) has the initial cardinality. The existential quantifier for c precedes the universal quantifier over target vertices. No finiteness assumption is imposed on the graph's vertex type."),
            Node("scaled-finite-mobility", "Scaled coordinate general position gives finite-configuration mobility",
                "scaled_finset_mobile", DescribeRole.Theorem, EndpointFormula(),
                "For every positive dimension and every nonempty finite coordinate general-position set S, its image under multiplication of every coordinate by four is infinitely mobile. The scaled image has exactly S.card vertices, so the common trajectory also has exactly S.card occupied vertices at every time."),
            Paragraph(Text("Take the single labelled trace supplied by IntegerLatticeMotion.scaled_finset_trace and let c(t) be the image of all labels at time t. Its initial image is exactly the fourfold image of S. Apply the original CylinderSevenTen.labelled_gp to obtain graph general position and CylinderSevenTen.labelled_move to obtain the exact one-robot legal transition. The injectivity and unchanged-label clauses ensure that the moved robot enters an unoccupied vertex. Apply CylinderSevenTen.configuration_card to preserve the exact number of occupied vertices. Nonemptiness supplies a fixed label, whose coverage of every vertex proves coverage by this same finite-configuration trajectory.")),
            Paragraph(Text("The trajectory starts at the scaled image. No trajectory from S to that image is asserted. The statement has no static cardinality optimum as a hypothesis or conclusion, and uses neither a finite box nor a finite traversal duration."))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(X(owner), Dot, X(name)))), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Finset(Formula v) => Call("Finset", v);
    private static Formula Card(Formula s) => Qualified("Finset", "card", s);
    private static Formula GP(Formula g, Formula s) => Qualified("CylinderSevenTen", "IsGeneralPosition", g, s);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(
        Operatorname, Grp(X("fun")), Sp, Seq(Open, X(name), Sp, Colon, Sp, type, Close), Sp, Mapsto, Sp, body);

    private static Formula MobilityBody(Formula v, Formula g, Formula s)
    {
        var c = X("c"); var t = X("t"); var x = X("x");
        var steps = All("t", Nat(), Qualified("CylinderSevenTen", "LegalMove", g,
            App(c, t), App(c, Add(t, D(1)))));
        var gp = All("t", Nat(), GP(g, App(c, t)));
        var cover = All("x", v, Ex("t", Nat(), Mem(x, App(c, t))));
        var cards = All("t", Nat(), Eq(Card(App(c, t)), Card(s)));
        return And(GP(g, s), Ex("c", Arrow(Nat(), Finset(v)),
            And(Eq(App(c, D(0)), s), And(steps, And(gp, And(cover, cards))))));
    }

    private static Formula MobilityFormula()
    {
        var v = X("V"); var g = X("G"); var s = X("S");
        return All("V", Call("Type"), Seq(OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            All("G", Call("SimpleGraph", v), All("S", Finset(v),
                Iff(Call("IsInfinitelyMobile", g, s), MobilityBody(v, g, s))))));
    }

    private static Formula EndpointFormula()
    {
        var k = X("k"); var v = Qualified("IntegerLatticeMotion", "Vertex", k); var s = X("S");
        var a = X("a"); var b = X("b"); var c = X("c");
        var gp = All("a", v, Imp(Mem(a, s), All("b", v, Imp(Mem(b, s),
            All("c", v, Imp(Mem(c, s), Imp(Ne(a, b), Imp(Ne(b, c), Imp(Ne(a, c),
                Not(Qualified("IntegerLatticeMotion", "Between", a, b, c)))))))))));
        var scaled = Qualified("Finset", "image", Lam("x", v, Lam("j", Call("Fin", k),
            Mul(D(4), App(X("x"), X("j"))))), s);
        var conclusion = And(Call("IsInfinitelyMobile", Qualified("IntegerLatticeMotion", "lattice", k), scaled),
            Eq(Card(scaled), Card(s)));
        return All("k", Nat(), Imp(Le(D(1), k), All("S", Finset(v),
            Imp(Qualified("Finset", "Nonempty", s), Imp(gp, conclusion)))));
    }
}
