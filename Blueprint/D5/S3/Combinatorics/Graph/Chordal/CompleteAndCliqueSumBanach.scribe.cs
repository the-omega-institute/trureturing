using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class CompleteAndCliqueSumBanachDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/CompleteAndCliqueSumBanach.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete graph has exact real Banach reconstruction coefficient (m minus two) over m. Separated clique sums admit a factor of two minus one over the maximum attachment size.",
        H("Complete graph constants and separated clique sums"),
        Blocks(
            Paragraph(Text("Write natcard for the natural-number cardinality and real for the natural-to-real cast. The norm is a seminorm for the upper estimates. Write skew(V,g) when every reversed gain is the negative of the original gain, including equal endpoints. Write triangle(V,g,e) when the norm of g(i,j)+g(j,l)-g(i,l) is at most e for every triple of pairwise distinct vertices. Write error(g,p,i,j) for the norm of g(i,j)-(p(j)-p(i)).")),
            Result("complete-graph-upper-bound", "completeGraph_banach_upper_bound",
                "Complete graph upper bound", UpperStatement(),
                "Average the star potentials with all possible centers. The residual on an ordered edge is the mean of the triangle expressions with each center. The two centers at the endpoints have zero residual. Each of the remaining centers contributes at most the triangle tolerance. The triangle inequality for the seminorm gives the stated coefficient."),
            Result("complete-graph-lower-bound", "completeGraph_banach_lower_bound",
                "Sharp complete graph lower bound", LowerStatement(),
                "The space ZeroDivSkew(m) consists of real m by m skew matrices whose row sums vanish, viewed as a real submodule with the supremum norm on matrix entries. Its finite dimension implies completeness. A signed triangle has entries of absolute value at most one, is skew and has zero row sums. Fix a root o and assign to (i,j) the signed triangle (o,i,j). The triangle defects are signed triangles. On its own coordinate (i,j), a gain with distinct endpoints has entry one if both endpoints differ from the root and zero otherwise. The sum over all ordered distinct pairs is (m minus one) times (m minus two). The corresponding sum for any potential differences vanishes by skew symmetry and the row sum equations. If every residual norm were smaller than the stated constant, the sum of residuals on their own edge coordinates would be strictly smaller than the gain sum, a contradiction."),
            Result("separated-clique-sum", "separatedCliqueSum_banach_gain_potential",
                "Midpoint averaging on separated clique sums", GlueStatement(),
                "Here S(a,b) is the intersection of the piece vertex sets P(a) and P(b). The cover condition assigns each vertex to a piece, and edgeCover requires the two endpoints of every graph edge to lie in a common piece. Attach requires every tree-edge intersection to be a nonempty clique of size at most m. DisjointNonneighbors requires disjoint pieces for distinct nonadjacent tree vertices. Separated requires, for each piece and any two distinct tree neighbors, that their attachment sets in that piece be disjoint and that no graph edge join these two sets. Fit means that the error on every ordered graph edge internal to its piece is at most R. Integrate along the unique paths from a tree root to shift each piece potential by a constant. For every attachment clique the mean of the difference of the shifted potentials is zero. Every two values of that difference differ in seminorm by at most twice R. Subtracting the mean and omitting the zero self-difference bounds half the mismatch by (one minus the reciprocal of the attachment size) times R. Separation implies each shared vertex belongs to exactly two pieces. Assign it the midpoint of the shifted potentials, and retain the shifted potential at each unshared vertex. On an edge inside a shared clique the residual is the mean of the two fitted residuals. Every other edge has at most one endpoint adjusted, so the radius increases by at most (one minus one over m) times R."))));

    private static DocumentBlock Result(string id, string name, string title, Formula formula, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Instance(string name, params Formula[] args) => Seq(OpenBracket, Call(name,args), CloseBracket, Sp);
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Error(Formula gain, Formula pot, Formula i, Formula j) => Call("error", gain, pot, i, j);
    private static Formula Coeff(Formula x) => Div(Sub(x,D(2)),x);
    private static Formula Space(Formula e, Formula body) => Seq(Instance("SeminormedAddCommGroup",e),
        Instance("NormedSpace",Reals,e),Comma,Sp,body);
    private static Formula U(Formula body) => All("u",Call("Universe"),All("v",Call("Universe"),body));

    private static Formula UpperStatement()
    {
        var v = V("V"); var e = V("E"); var g = V("g"); var eps = V("epsilon");
        var p = V("phi"); var i = V("i"); var j = V("j");
        var card = Call("natcard",v);
        Formula result = Some("phi",Arrow(v,e),All("i",v,All("j",v,
            Imp(Ne(i,j),Le(Error(g,p,i,j),Mul(Coeff(Call("real",card)),eps))))));
        result = All("g",Arrow(v,Arrow(v,e)),All("epsilon",Reals,
            Imp(Le(D(0),eps),Imp(Call("skew",v,g),Imp(Call("triangle",v,g,eps),result)))));
        return U(All("V",Call("Type",V("u")),Seq(Instance("Finite",v),Comma,Sp,
            Imp(Le(D(2),card),All("E",Call("Type",V("v")),Space(e,result))))));
    }

    private static Formula LowerStatement()
    {
        var m = V("m"); var v = Call("Fin",m); var e = Call("ZeroDivSkew",m);
        var g = V("g"); var p = V("phi"); var i = V("i"); var j = V("j");
        Formula bound = All("phi",Arrow(v,e),Some("i",v,Some("j",v,
            And(Ne(i,j),Le(Coeff(Call("real",m)),Error(g,p,i,j))))));
        return All("m",Naturals,Imp(Le(D(2),m),Some("g",Arrow(v,Arrow(v,e)),
            And(Call("skew",v,g),And(Call("triangle",v,g,D(1)),bound)))));
    }

    private static Formula GlueStatement()
    {
        var i = V("I"); var v = V("V"); var e = V("E"); var t = V("T"); var gph = V("G");
        var p = V("P"); var m = V("m"); var g = V("g"); var r = V("R"); var local = V("phi");
        var f = V("Phi"); var x = V("x"); var y = V("y");
        Formula result = Some("Phi",Arrow(v,e),All("x",v,All("y",v,
            Imp(Call("Adj",gph,x,y),Le(Error(g,f,x,y),Mul(Par(Sub(D(2),Div(D(1),Call("real",m)))),r))))));
        result = All("g",Arrow(v,Arrow(v,e)),All("R",Reals,Imp(Le(D(0),r),
            All("phi",Arrow(i,Arrow(v,e)),Imp(Call("Fit",gph,p,g,local,r),result)))));
        result = All("m",Naturals,Imp(Le(D(1),m),Imp(Call("Attach",t,gph,p,m),
            Imp(Call("DisjointNonneighbors",t,p),Imp(Call("Separated",t,gph,p),result)))));
        result = All("T",Call("SimpleGraph",i),Imp(Call("IsTree",t),All("G",Call("SimpleGraph",v),
            All("P",Arrow(i,Call("Set",v)),Imp(Call("cover",v,p),Imp(Call("edgeCover",gph,p),result))))));
        return U(All("w",Call("Universe"),All("I",Call("Type",V("w")),
            All("V",Call("Type",V("u")),Seq(Instance("Finite",v),Comma,Sp,
                All("E",Call("Type",V("v")),Space(e,result)))))));
    }
}

