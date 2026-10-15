using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class SparseProbeCoercivityDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Quantum/QuantumChannels/SparseProbeCoercivity.";
    private static DocumentBlock Node(string id,string name,Formula f,string text,DescribeRole role=DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(name),
            StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coordinate basis and one unit vector of full support control the Hilbert--Schmidt distance to scalar matrices.",
        H("Complex sparse-probe coercivity"),Blocks(
            Node("hs-square","hsSq",Definition("hsSq",false),"hsSq is the sum of the squared complex moduli of all matrix entries."),
            Node("off-square","offSq",Definition("offSq",true),"offSq is the corresponding sum over unequal row and column indices."),
            Node("survival-loss","survivalLoss",LossFormula(false),"The survival loss is the squared norm of Cv minus the squared modulus of its inner product with the unit probe v. For a complete Kraus family its sum is the loss of the rank-one survival event."),
            Node("probe-loss","probeLoss",LossFormula(true),"The coordinate losses sum to offSq. The additional probe contributes survivalLoss, so there are d+1 survival events."),
            Node("hs-split","hs_split",SplitFormula(),"Separating the diagonal entries gives the Hilbert--Schmidt decomposition.",DescribeRole.Lemma),
            Node("sparse-probe-coercivity","sparse_probe_coercivity",CoercivityFormula(),
                "Let c be the complex inner product of v with Cv, and let B be the off-diagonal part of C. The diagonal residual (Cii-c)vi is (Cv-cv)i-(Bv)i. Its squared norm is at most twice the sum of the two squared norms. The unit-vector Cauchy--Schwarz estimate bounds the squared norm of Bv by offSq. Full support bounds the unweighted diagonal residual by its weighted counterpart divided by mu. The trace mean minimizes the unweighted residual, giving the displayed coefficient mu/(2+mu). The argument allows arbitrary complex matrices; no real, Hermitian, or unital condition is present.",DescribeRole.Theorem))));
    private static Formula V(string n) => F.Id(n);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string n, params Formula[] x) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula.BoundVariable[] b, Formula p) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. b], p);
    private static Formula Rel(Formula x, FormulaRelationOperator r, Formula y) => new Formula.Relation(x, r, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => Rel(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Fin(Formula d) => Call("Fin",d);
    private static Formula Mat(Formula d) => Call("Matrix",Fin(d),Fin(d),C);
    private static Formula Vec(Formula d) => Seq(Fin(d), Sp, To, Sp, C);
    private static Formula Sum(string i, Formula domain, Formula f) => Seq(F.Sum, Underscore, Grp(V(i), Sp, Colon, Sp, domain), Sp, f);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula At(Formula f, params Formula[] x) => Seq(f, Sp, Parenthesized(x.Length == 1 ? x[0] : Seq(x[0], Comma, Sp, x[1])));
    private static Formula Norm(Formula x) => Call("normSq",x);

    private static Formula Definition(string name,bool off)
    {
        Formula d=V("d"), m=V("M"), i=V("i"), j=V("j");
        Formula x=Norm(At(m,i,j));
        if(off) x=Call("ite",Eq(i,j),Num(0),x);
        return All([B("d",N),B("M",Mat(d))],Eq(Call(name,m),Sum("i",Fin(d),Sum("j",Fin(d),x))));
    }
    private static Formula LossFormula(bool combined)
    {
        Formula d=V("d"), m=V("M"), v=V("v"), i=V("i");
        Formula value=combined?Add(Call("offSq",m),Call("survivalLoss",m,v)):
            Sub(Sum("i",Fin(d),Norm(At(Call("mulVec",m,v),i))),
                Norm(Sum("i",Fin(d),Mul(Call("conj",At(v,i)),At(Call("mulVec",m,v),i)))));
        return All([B("d",N),B("M",Mat(d)),B("v",Vec(d))],Eq(Call(combined?"probeLoss":"survivalLoss",m,v),value));
    }
    private static Formula SplitFormula()
    {
        Formula d=V("d"),m=V("M"),i=V("i");
        return All([B("d",N),B("M",Mat(d))],Eq(Call("hsSq",m),Add(Call("offSq",m),Sum("i",Fin(d),Norm(At(m,i,i))))));
    }
    private static Formula CoercivityFormula()
    {
        Formula d=V("d"),m=V("M"),v=V("v"),mu=V("mu"),i=V("i");
        Formula h=And(Rel(Num(0),FormulaRelationOperator.LessThan,d),And(Eq(Sum("i",Fin(d),Norm(At(v,i))),Num(1)),
            And(Rel(Num(0),FormulaRelationOperator.LessThan,mu),All([B("i",Fin(d))],Le(mu,Norm(At(v,i)))))));
        return All([B("d",N),B("M",Mat(d)),B("v",Vec(d)),B("mu",R)],Imp(h,
            Le(Mul(Frac(mu,Add(Num(2),mu)),Sub(Call("hsSq",m),Frac(Norm(Call("trace",m)),d))),Call("probeLoss",m,v))));
    }
}
