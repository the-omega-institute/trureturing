using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras.HuEvolutionCriterionFormula;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal static class HuEvolutionCriterionFormula
{
    internal static Formula Named(string s, params Formula[] a) => Call(Seq(Operatorname, Grp(F.Id(s))), a);
    internal static Formula Call(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    internal static Formula V(string s) => F.Id(s);
    internal static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    internal static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    internal static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    internal static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    internal static Formula Coord(Formula d) => Named("Coord", d);
    internal static Formula Product(Formula d) => Named("Product", d);
    internal static Formula Fin(Formula d) => Named("Fin", d);
    internal static DocumentBlock.Describe Def(string prefix, string name, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(prefix + name), H(title),
            StatementSource.FromAuthor(f), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}

internal sealed class HuEvolutionCodimensionOneCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/HuEvolutionCodimensionOneCriterion.";
    private static Formula Matrix(Formula m) => Named("Matrix", Fin(m), Fin(m), C);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Shift(Formula a, Formula t) => Subtract(t, Mul(new Formula.Fraction(a, D(2)), D(1)));
    private static Formula Law(Formula m, Formula a, Formula c, Formula t, Formula mu) =>
        All("x", Coord(Add(m, D(1))), All("y", Coord(Add(m, D(1))),
            Eq(Call(mu, V("x"), V("y")), Named("codimOneProduct", m, a, c, t, V("x"), V("y")))));
    public DocumentDefinition Create()
    {
        var m = V("m"); var a = V("a"); var c = V("c"); var t = V("T"); var mu = V("mu");
        var n = Shift(a, t);
        var criterion = All("m", N, Imp(Le(D(1), m), All("a", C, Imp(Ne(a, D(0)),
            All("c", Coord(m), All("T", Matrix(m), Imp(Ne(Named("det", t), D(0)),
                All("mu", Product(Add(m, D(1))), Imp(Law(m, a, c, t, mu),
                    Iff(Named("minimalPerfect", mu), And(Eq(Pow(n, m), D(0)),
                        Ne(Named("det", Named("krylov", n, c, m)), D(0)))))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An exact all-parameter nilpotent and cyclic criterion for minimal perfect algebras with a square-zero hyperplane.",
            H("A codimension-one minimal-perfect criterion"), Blocks(
                Def(Prefix, "codimOneProduct", "The square-zero hyperplane product", ProductFormula(),
                    "Coordinate zero is the quotient vector u; coordinate i.succ is the i-th coordinate of W. "
                    + "Here tail(x)(j)=x(j.succ). "
                    + "The law is u squared = au+c, uw=wu=Tw and W squared =0. Matrices act on column vectors. "
                    + "There is no assumption of associativity, a unit, a natural basis or a Jordan identity."),
                Describe.Lean(DescribeId.Create("codimension-one-criterion"),
                    DeclarationHandle.Create(Prefix + "codimension_one_criterion"),
                    H("The complete nilpotent and cyclic equivalence"), StatementSource.FromAuthor(Disp(criterion)),
                    AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuadraticForms/hu2026idempotent")),
                    Blocks(
                        Paragraph(Text("The criterion and its source proof are due to Wenlin Zhang and Haobo Ma, "
                            + "Structure tests for stable derived terms, section 2, criterion (4) and identity (5). "
                            + "The authored source has SHA256 1051e84fd643f3c3c528c8eb000fcecd2796054aadf6d2aa855815ad91192222. "
                            + "No public-priority claim is made. "
                            + "Hu and Wen, arXiv:2609.25023v1, Theorem 2.1, Lemma 2.3 and Proposition 2.4 include the boundary example "
                            + "m=1, a=2, T=1, c=−1 at their parameter 2.")),
                        Paragraph(Text("García-Martínez and Pérez-Rodríguez, DOI 10.1007/s00013-026-02251-0, Theorems 2.1 and 3.5, "
                            + "and Ladra and Pérez-Rodríguez, DOI 10.5802/crmath.804, Theorem 2 and Corollary 4, treat regular evolution algebras "
                            + "with natural bases. Kaygorodov and Volkov, arXiv:1710.08943v2, section 4, Lemma 4.1, impose generation type one. "
                            + "Those additional hypotheses are absent here; none of these results is used as an arbitrary-subspace minimality criterion.")),
                        Paragraph(Text("In the displayed formula, 1 is the m by m identity matrix. "
                            + "The matrix krylov(N,c,m) has entry (i,j) equal to ((N raised to j.val).mulVec c)(i). "
                            + "Its columns are c,Nc,...,N raised to m−1 times c, in that order. "
                            + "The exponent is exactly m. Arbitrary c, including zero, and every complex subspace are included. "
                            + "The square of a subspace means the span of all pair products. "
                            + "Minimal perfect means V squared = V and every nonzero complex subspace U "
                            + "satisfying U squared = U equals V.")),
                        Paragraph(Text("A nonzero perfect subspace contains a normalized vector u+z. Its intersection S with W "
                            + "is invariant under T and N, and contains c+2Nz. Cyclicity puts W inside S+NW. "
                            + "Repeated lifting gives W=S+N raised to m times W=S, so the subspace is the whole algebra.")),
                        Paragraph(Text("Conversely, an invariant subspace S containing c+2Nz gives the subspace generated by u+z and S. "
                            + "It is closed under multiplication. Left multiplication by u+z is injective because a and T are invertible; "
                            + "its restriction is therefore surjective, proving equality with its full product span. "
                            + "The Fitting generalized-zero component supplies a proper such subspace when N is not nilpotent. "
                            + "When N is nilpotent but c is not cyclic, its finite orbit span supplies one instead.")),
                        Paragraph(Text("The arbitrary-operator-to-Jordan product-preserving isomorphism, the idempotent obstruction, "
                            + "square-zero extensions and Hu–Wen Question 2.11 are separate assertions and do not follow as completion claims here."))),
                    DescribeRole.Theorem)), []));
    }
    private static Formula ProductFormula()
    {
        var m=V("m"); var a=V("a"); var c=V("c"); var t=V("T"); var x=V("x"); var y=V("y");
        var p=Named("codimOneProduct",m,a,c,t,x,y); var xz=Call(x,D(0)); var yz=Call(y,D(0)); var i=V("i");
        var tail=Add(Add(Mul(xz,Call(Named("mulVec",t,Named("tail",y)),i)),
            Mul(yz,Call(Named("mulVec",t,Named("tail",x)),i))), Mul(Mul(Call(c,i),xz),yz));
        return Disp(All("m",N,All("a",C,All("c",Coord(m),All("T",Matrix(m),
            All("x",Coord(Add(m,D(1))),All("y",Coord(Add(m,D(1))),
                And(Eq(Call(p,D(0)),Mul(Mul(a,xz),yz)),
                    All("i",Fin(m),Eq(Call(p,Named("succ",i)),tail))))))))));
    }
}
