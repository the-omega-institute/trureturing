using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationApproximation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same integer exponent approximates both logarithmic coordinates of a complex target.",
        H("Joint logarithmic power-root approximation"), Blocks(
            Paragraph(Text("The complex exponential is the existing Mathlib exponential. No graph or density hypothesis enters this analytic lemma. The conclusion chooses a single natural exponent for both the modulus and angle; it does not combine separately optimal branches.")),
            Node("joint_power_root_approximation", "Joint radial and angular approximation", Approximation(),
                "For every complex xi with nonzero real part and every positive real epsilon there is a natural N such that, for all real t and alpha with N+2<t/xi.re, there exist a positive natural k and a complex w satisfying w^k=exp(t+alpha*I) and norm(w-exp(xi))<epsilon. Let p=t/xi.re and k=floor(p). The same k obeys k>N and abs(t/k-xi.re)<=abs(xi.re)/k. Round (k*xi.im-alpha)/(2*pi) to an integer j and set v=t/k+((alpha+2*pi*j)/k)*I. Exact exponential periodicity gives (exp(v))^k=exp(t+alpha*I), while abs(v.im-xi.im)<=pi/k. Thus norm(v-xi)<delta for the continuity radius delta of exp at xi. The bound on N is chosen before t and alpha. This is an elementary logarithmic approximation ingredient, with all rounding, powers and continuity checked in Lean; no literature-priority claim is made.")), []));

    private static DocumentBlock Node(string selector, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("td-approx-" + selector.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Cast(Formula x, Formula t) => Par(Seq(x,Colon,t));
    private static Formula Pow(Formula x, Formula n) => Seq(Par(x),Caret,Grp(n));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula And(params Formula[] xs) => xs.Length==1 ? xs[0] : new Formula.Logic(Par(xs[0]),FormulaLogicOperator.And,Par(And(xs[1..])));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x),FormulaLogicOperator.Implies,Par(y));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists,Sp,Par(Seq(V(s),Colon,t)),Comma,Sp,b);
    private static Formula Graph(Formula t) => Call("SimpleGraph",t);
    private static Formula Norm(Formula x) => Seq(Vert,Sp,x,Vert);
    private static Formula Approximation() => All("xi",Complex,Imp(Ne(Call("re",V("xi")),D(0)),All("epsilon",Real,Imp(Lt(D(0),V("epsilon")),Some("N",Nat,All("t",Real,All("alpha",Real,Imp(Lt(Add(Cast(V("N"),Real),D(2)),new Formula.Fraction(V("t"),Call("re",V("xi")))),Some("k",Nat,Some("w",Complex,And(Lt(D(0),V("k")),Eq(Pow(V("w"),V("k")),Call("exp",Add(Cast(V("t"),Complex),Mul(Cast(V("alpha"),Complex),Call("I"))))),Lt(Norm(Sub(V("w"),Call("exp",V("xi")))),V("epsilon")))))))))))));
}
