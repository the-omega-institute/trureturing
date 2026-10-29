using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.GeneralPosition;

internal sealed class IntegerLatticeMotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/GeneralPosition/IntegerLatticeMotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-unit integer lattice distances and one common serialized covering trace for scaled finite general-position configurations.",
        H("Integer lattice geometry and serialized translations"),
        Blocks(
            Paragraph(Text("The declarations are in D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMotion. In the formulas, OnGeodesic denotes CylinderSevenTen.OnGeodesic; Connected, Adj and dist are the SimpleGraph operations; image, univ, card and Nonempty are Finset operations; range is Set.range and natAbs is Int.natAbs. The vertex set consists of integer-valued functions on Fin k. An edge changes one coordinate by one in either direction and leaves every other coordinate fixed. Distances are graph distances in this concrete graph.")),
            Node("vertices", "Integer lattice vertices", "Vertex", DescribeRole.Definition,
                All("k", Nat(), Eq(V(X("k")), Arrow(Fin(X("k")), Int()))),
                "A vertex records all k integer coordinates."),
            Node("edges", "Exactly one signed unit coordinate change", "lattice", DescribeRole.Definition,
                EdgeFormula(), "The changed coordinate is specified by an existential index. The signed difference is one, and every other coordinate agrees."),
            Node("sum-distance", "The sum of coordinate distances", "l1", DescribeRole.Definition,
                KXYZ(false, Eq(Call("l1", X("x"), X("y")),
                    SumOver("j", Fin(X("k")), Call("natAbs", Sub(App(X("x"), X("j")), App(X("y"), X("j"))))))),
                "The metric is the sum of integer absolute differences. It is independent of the sup metric supplied by the usual function-space metric instance."),
            Node("distance", "Connectivity and exact graph distance", "lattice_distance", DescribeRole.Theorem,
                All("k", Nat(), And(Call("Connected", G()),
                    All("x", V(X("k")), All("y", V(X("k")),
                        Eq(Call("dist", G(), X("x"), X("y")), Call("l1", X("x"), X("y"))))))),
                "The distance certificate from WellCoveredPowerCliqueProduct is applied directly. Each edge changes the sum of distances to a target by at most one. A vertex different from the target has a coordinate that can move one unit toward the target and reduce the sum by exactly one. This constructs walks of precisely the claimed length and proves the reverse lower bound."),
            Node("between", "Coordinatewise betweenness", "Between", DescribeRole.Definition,
                KXYZ(true, Iff(Call("Between", X("x"), X("y"), X("z")),
                    All("j", Fin(X("k")), CoordinateBetween()))),
                "The coordinate orientations can differ. In each coordinate the middle value lies between the endpoint values, allowing equality."),
            Node("geodesic", "The coordinate and graph conditions coincide", "between_iff_geodesic", DescribeRole.Theorem,
                KXYZ(true, Iff(Call("Between", X("x"), X("y"), X("z")),
                    Call("OnGeodesic", G(), X("x"), X("y"), X("z")))),
                "This is a consumed bind-only bridge on the live path from scaled_finset_trace through perturb_no_geodesic and mixed_no_geodesic to between_iff_geodesic; it is not independent content. Equality in the sum triangle inequality holds exactly when it holds in every coordinate. The integer absolute-value equality in each coordinate is equivalent to either of the two order orientations."),
            Node("trace", "One scaled labelled covering trace", "ScaledCoveringTrace", DescribeRole.Definition,
                TraceFormula(),
                "The initial positions are four times the original labelled vertices. Positions remain injective and no triple of distinct labels lies on a graph geodesic. At every natural time a single specified label moves along a graph edge into a vertex outside the previous range, and every other label stays fixed. Each fixed label eventually visits every vertex. The same trace serves all targets."),
            Node("finite-trace", "A trace for every nonempty finite coordinate general-position set", "scaled_finset_trace", DescribeRole.Theorem,
                FinsetFormula(),
                "For every positive dimension, the finite labels enumerate exactly the given nonempty finite set. The one common trace starts at the scaled set 4S, not at the original S. Scaling by four allows each robot an individual coordinate perturbation between minus one and one: any order relation between perturbed coordinates reflects an order relation before perturbation, so coordinate betweenness cannot be created. For each unit translation the robots move one at a time in label order. At time m q plus r, the first r labels have moved from translation q to translation q plus one. The last move of a block moves only the last label. A countable enumeration of lattice vertices is followed by finite distance descent toward successive targets; after reaching a target, a forced positive coordinate edge advances to the next target. Thus repeated enumeration values never introduce a stationary step. At block boundaries all labels have completed the same translation, and surjectivity of the common translation walk makes every fixed robot cover the entire lattice."),
            Paragraph(Text("The result supplies the complete labelled trace and the exact finite-set enumeration. It does not state the static maximum cardinality or an attained mobile general-position number. Finite occupied sets are obtained as the images of the labels at each time; conversion to the existing CylinderSevenTen.LegalMove relation is a separate finite-configuration obligation."))),
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
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(
        Operatorname, Grp(X("fun")), Sp, Seq(Open, X(name), Sp, Colon, Sp, type, Close), Sp, Mapsto, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, Open, a, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Int() => Call("Int");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula V(Formula k) => Call("Vertex", k);
    private static Formula G() => Call("lattice", X("k"));
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(X(name), Sp, Colon, Sp, type)), Sp, Seq(Open, body, Close));
    private static Formula KXYZ(bool third, Formula body) => All("k", Nat(),
        All("x", V(X("k")), All("y", V(X("k")), third ? All("z", V(X("k")), body) : body)));
    private static Formula At(Formula p, Formula t, Formula i) => App(p, t, i);
    private static Formula Distinct(Formula a, Formula b, Formula c, Formula body) =>
        Imp(Ne(a,b), Imp(Ne(b,c), Imp(Ne(a,c), body)));

    private static Formula EdgeFormula()
    {
        var k = X("k"); var x = X("x"); var y = X("y"); var j = X("j"); var i = X("i");
        return KXYZ(false, Iff(Call("Adj", G(), x, y), Ex("j", Fin(k),
            And(Or(Eq(App(y,j), Add(App(x,j),D(1))), Eq(App(y,j), Sub(App(x,j),D(1)))),
                All("i", Fin(k), Imp(Ne(i,j), Eq(App(y,i),App(x,i))))))));
    }

    private static Formula CoordinateBetween()
    {
        var j = X("j"); var x = App(X("x"),j); var y = App(X("y"),j); var z = App(X("z"),j);
        return Or(And(Le(x,y),Le(y,z)),And(Le(z,y),Le(y,x)));
    }

    private static Formula TraceFormula()
    {
        var k = X("k"); var m = X("m"); var s = X("s"); var p = X("p");
        return All("k",Nat(),All("m",Nat(),All("s",Arrow(Fin(m),V(k)),
            All("p",Arrow(Nat(),Arrow(Fin(m),V(k))),
                Iff(Call("ScaledCoveringTrace",s,p),TraceBody(k,m,s,p))))));
    }

    private static Formula TraceBody(Formula k, Formula m, Formula s, Formula p)
    {
        var t = X("t"); var i = X("i"); var a = X("a"); var b = X("b"); var c = X("c");
        var start = All("i",Fin(m),Eq(At(p,D(0),i),
            Lam("j",Fin(k),Mul(D(4),App(s,i,X("j"))))));
        var inj = All("t",Nat(),Call("Injective",App(p,t)));
        var gp = All("t",Nat(),All("a",Fin(m),All("b",Fin(m),All("c",Fin(m),
            Distinct(a,b,c,Not(Call("OnGeodesic",G(),At(p,t,a),At(p,t,b),At(p,t,c))))))));
        var step = All("t",Nat(),Ex("i",Fin(m),And(
            Call("Adj",G(),At(p,t,i),At(p,Add(t,D(1)),i)),And(
                All("a",Fin(m),Imp(Ne(a,i),Eq(At(p,t,a),At(p,Add(t,D(1)),a)))),
                Not(Mem(At(p,Add(t,D(1)),i),Call("range",App(p,t))))))));
        var cover = All("i",Fin(m),All("x",V(k),Ex("t",Nat(),Eq(At(p,t,i),X("x")))));
        return And(start,And(inj,And(gp,And(step,cover))));
    }

    private static Formula FinsetFormula()
    {
        var k = X("k"); var set = X("S"); var s = X("s"); var p = X("p");
        var a = X("a"); var b = X("b"); var c = X("c");
        var n = Call("card",set);
        var gp = All("a",V(k),Imp(Mem(a,set),All("b",V(k),Imp(Mem(b,set),
            All("c",V(k),Imp(Mem(c,set),Distinct(a,b,c,Not(Call("Between",a,b,c)))))))));
        var result = Ex("s",Arrow(Fin(n),V(k)),Ex("p",Arrow(Nat(),Arrow(Fin(n),V(k))),
            And(Call("Injective",s),And(Eq(Call("image",s,Call("univ")),set),
                Call("ScaledCoveringTrace",s,p)))));
        return All("k",Nat(),Imp(Le(D(1),k),All("S",Call("Finset",V(k)),
            Imp(Call("Nonempty",set),Imp(gp,result)))));
    }
}
