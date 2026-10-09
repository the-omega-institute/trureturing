using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class TwoInvolutionWordRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous operator words in two involutions with a four-dimensional relative-product space.",
        H("Two involutions and homogeneous word rank"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-involution-homogeneous-word-rank"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.homogeneous_word_rank"),
                H("Exact rank at every length"), StatementSource.FromAuthor(RankFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A is a finite-dimensional complex algebra, with no commutativity assumption. "
                        + "Products(u,v,0) is {1}; Products(u,v,n+1) consists of u and v multiplied on the left "
                        + "of every exact length-n product. W is its complex linear span. P is the span of "
                        + "1, uv, (uv)^2 and (uv)^3. The two closure hypotheses are left multiplication by uv "
                        + "and vu on every member of P.")),
                    Paragraph(Text("The proof places even and odd word spaces in P and uP. "
                        + "Invertible multiplication exhibits one, two, three and four independent words at "
                        + "lengths zero through three. Rank monotonicity and the invariant space give every "
                        + "later length. This theorem concerns terminal operator spans and supplies no measured "
                        + "history, physical implementation or independent coherent archive."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-involution-word-space-scale"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_scale"),
                H("Nonzero generator scaling"), StatementSource.FromAuthor(ScaleFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Independent nonzero complex weights preserve each homogeneous span. The lifted balanced "
                    + "five-mode theorem consumes this auxiliary result in its live proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-involution-word-space-map"),
                DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/TwoInvolutionWordRank.wordSpace_map"),
                H("Exact algebra transport"), StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A unital complex algebra homomorphism maps the entire exact-length product set, including "
                    + "the empty product. The lifted balanced five-mode theorem consumes this auxiliary equality; "
                    + "injectivity is needed there to preserve dimension."))), DescribeRole.Theorem))));

    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string n, params Formula[] x) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula.BoundVariable[] bs, Formula p) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], p);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula W(Formula u, Formula v, Formula n) => Call("wordSpace", u, v, n);
    private static Formula RankFormula()
    {
        Formula a=F.Id("A"), u=F.Id("u"), v=F.Id("v"), n=F.Id("n"), x=F.Id("x");
        Formula p=Call("powerSpace",u,v);
        Formula Closure(Formula r) => All([B("x",a)], Imp(
            new Formula.Relation(x,FormulaRelationOperator.MemberOf,p),
            new Formula.Relation(Mul(r,x),FormulaRelationOperator.MemberOf,p)));
        Formula h=And(And(Eq(Mul(u,u),Num(1)),Eq(Mul(v,v),Num(1))),
            And(Call("LinearIndependent",C,Call("firstFourPowers",Mul(u,v))),
                And(Closure(Mul(u,v)),Closure(Mul(v,u)))));
        return Disp(All([B("A",Call("FiniteDimensionalComplexAlgebra")),B("u",a),B("v",a),B("n",N)],
            Imp(h,Eq(Call("finrank",C,W(u,v,n)),Call("min",Add(n,Num(1)),Num(4))))));
    }
    private static Formula ScaleFormula()
    {
        Formula a=F.Id("A"), u=F.Id("u"), v=F.Id("v"), z=F.Id("z"), w=F.Id("w"), n=F.Id("n");
        Formula nz(Formula x) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,Num(0));
        return Disp(All([B("A",Call("FiniteDimensionalComplexAlgebra")),B("u",a),B("v",a),
            B("z",C),B("w",C),B("n",N)], Imp(And(nz(z),nz(w)),
            Eq(W(Call("smul",z,u),Call("smul",w,v),n),W(u,v,n)))));
    }
    private static Formula MapFormula()
    {
        Formula a=F.Id("A"), e=F.Id("E"), f=F.Id("f"), u=F.Id("u"), v=F.Id("v"), n=F.Id("n");
        return Disp(All([B("A",Call("FiniteDimensionalComplexAlgebra")),B("E",Call("ComplexAlgebra")),
            B("f",Call("AlgHom",C,a,e)),B("u",a),B("v",a),B("n",N)],
            Eq(W(Call("apply",f,u),Call("apply",f,v),n),Call("map",W(u,v,n),Call("toLinearMap",f)))));
    }
}
