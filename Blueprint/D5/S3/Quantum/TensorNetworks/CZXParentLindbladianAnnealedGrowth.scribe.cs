using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class CZXParentLindbladianAnnealedGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/CZXParentLindbladianAnnealedGrowth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative annealed Euclidean row growth for the four CZX transfer letters.",
        H("Four-letter annealed row growth"),
        Blocks(
            Paragraph(Text("The rows are real two-dimensional Euclidean vectors. Each letter is chosen uniformly from two matrix types and two signs. Products retain their natural left-to-right order, and the empty product is the identity. The bound controls the first norm moment with a strict improvement over the square root of its second-moment multiplier.")),
            Node("Row", "Euclidean rows", Eqn(Local("Row"), Call("EuclideanSpace", Real(), Fin(D(2)))), "The carrier is the standard real Euclidean space on two coordinates."),
            Node("Letter", "The four-letter alphabet", Eqn(Local("Letter"), Product(Fin(D(2)), Fin(D(2)))), "The first coordinate selects the matrix type. The second selects the signs +1 and -1."),
            Node("letter", "The transfer matrices", LetterStatement(), "For e=+1 or -1, the type-zero letter is [[1+rho,2e rho],[0,1-rho]], and the type-one letter is [[1-rho,0],[2e rho,1+rho]]. Both signs and both types have weight one quarter."),
            Node("rowAction", "Right matrix action", ActionStatement(), "The ordinary row-matrix product is transported to the Euclidean carrier. Its norm is sqrt(a squared plus b squared), rather than the supremum norm on coordinate functions."),
            Node("word", "Ordered words", WordStatement(), "A length k+1 word is its length k prefix followed by its last letter on the right. Consequently W_k=S(w_0)...S(w_(k-1)) in increasing index order, with W_0=I."),
            Node("average", "Normalized uniform average", AverageStatement(), "The normalization is 4 to the power minus k, and the sum ranges over every function from Fin k to the four-letter alphabet. This includes the unique empty word and every real row, including zero."),
            Node("growthFactor", "Explicit growth factor", FactorStatement(), "The factor q is sqrt(1+3 rho squared) minus rho squared times (1-rho) squared divided by 2(1+3rho) cubed."),
            Node("annealed_growth", "All-length Euclidean growth estimate", GrowthStatement(), "For every rho strictly between zero and one, every natural length k, and every real row v, the normalized average is at most q to the power k times the Euclidean norm of v. The factor satisfies 1<q<sqrt(1+3rho squared)<2, so this is a growth estimate.", DescribeRole.Theorem),
            Paragraph(Text("Write s=a squared+b squared, d=a squared-b squared, mu=1+3rho squared, and K=1+3rho. The four squared output norms Y have mean mu s and variance 4rho squared(1-rho) squared s squared+16rho cubed d squared. Each lies between zero and K squared s. On a unit row, the quantitative inequality sqrt(y)<=sqrt(mu)+(y-mu)/(2sqrt(mu))-(y-mu) squared/(8K cubed) applies even at y=0. To see this, set u=sqrt(y), z=sqrt(mu). The remainder has numerator (u-z) squared times [4K cubed-z(u+z) squared], and the bracket equals 4K squared(K-z)+z(2K-u-z)(2K+u+z), which is nonnegative. Averaging cancels the linear term; the positive variance floor supplies the explicit subtraction in q. Positive homogeneity extends the estimate to arbitrary rows. Splitting a word into its prefix and final letter applies that estimate to the actual prefix row at every induction step.")),
            Paragraph(Text("At k=0 the bound is equality for every row, and at v=0 it is equality at every length. At rho=0 the formula gives q=1, and at rho=1 it gives q=2; the strict interior inequalities exclude these endpoints.")),
            Paragraph(Text("Prospective CZX trace-distance consequence.")),
            Paragraph(Text("The intended quantum application uses exactly the original even-window rate-one CZX evolution, n=2m>=4, t>0, rho=exp(-t), A0=4^(-m)(I+tensorX(n)), and sigma=4^(-m)(I+2^(1-m)czxUnitary(n)). For Delta=FiniteTraceDistance.traceNorm(evolution(n,t,A0)-sigma)/2, the intended consequence is Delta<=2sqrt(2)(q(rho)/2)^m. This quantum statement is not established by the present formal theorem.")),
            Paragraph(Text("The missing formal steps are the actual finite-time coefficient action and exponential product on the original even starts; the all-size cyclic pair bijection and variable-real ordered transfer contraction, retaining both ordered windows when m=2; the canonical trace-norm evaluation on U diag(f), with the exact normalization and stationary subtraction; and combination on those original quantum endpoints. A projective pressure operator and spectral-radius limit are separate questions. The improved exponential base comes with a larger prefactor than the older Hilbert-Schmidt asymptotic estimate, so it does not imply dominance at every finite size."))
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("czx-growth-" + name.ToLowerInvariant().Replace("_", "-") + (name == "Row" || name == "Letter" ? "-type" : "")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Q(string name)
    {
        var parts = name.Split('.');
        var items = new List<Formula> { Operatorname, Grp(F.Id(parts[0])) };
        for (var i = 1; i < parts.Length; i++) items.AddRange([Dot, Grp(F.Id(parts[i]))]);
        return Seq(items.ToArray());
    }
    private static Formula Local(string name) => Q(Prefix.Replace('/', '.') + name);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => At(Q(name), args);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => P(Seq(x, Colon, Sp, t));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Typed(F.Id(n), t), Comma, Sp, b);
    private static Formula Lam(string n, Formula t, Formula b) => Seq(LambdaLower, Sp, Typed(F.Id(n), t), Sp, Mapsto, Sp, P(b));
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Add, P(y));
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Subtract, P(y));
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(P(x), FormulaBinaryOperator.Multiply, P(y));
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(P(x), y);
    private static Formula Product(Formula x, Formula y) => Call("Prod", x, y);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(P(x), P(y));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Row() => Local("Row");
    private static Formula Alphabet() => Local("Letter");
    private static Formula Matrix() => Call("Matrix", Fin(D(2)), Fin(D(2)), Real());
    private static Formula Words(Formula k) => Arrow(Fin(k), Alphabet());
    private static Formula Norm(Formula v) => Call("norm", v);
    private static Formula Mu(Formula r) => Add(D(1), Mul(D(3), Pow(r, D(2))));
    private static Formula Root(Formula r) => Call("Real.sqrt", Mu(r));
    private static Formula Factor(Formula r) => At(Local("growthFactor"), r);
    private static Formula Avg(Formula r, Formula k, Formula v) => At(Local("average"), r, k, v);
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(new Formula.Subscript(Sum, Seq(F.Id(n), Colon, Sp, t)), Sp, b);

    private static Formula LetterStatement()
    {
        var r=F.Id("rho"); var c=F.Id("c"); var e=F.Id("e");
        Formula sign=Call("ite", Eqn(Call("Prod.snd",c),D(0)), D(1), Seq(Minus,D(1)));
        Formula a=Seq(Begin,Grp(F.Id("pmatrix")),Add(D(1),r),Amp,Mul(Mul(D(2),e),r),RowBreak,D(0),Amp,Sub(D(1),r),End,Grp(F.Id("pmatrix")));
        Formula b=Seq(Begin,Grp(F.Id("pmatrix")),Sub(D(1),r),Amp,D(0),RowBreak,Mul(Mul(D(2),e),r),Amp,Add(D(1),r),End,Grp(F.Id("pmatrix")));
        return All("rho",Real(),All("c",Alphabet(),Eqn(At(Local("letter"),r,c),
            At(P(Lam("e",Real(),Call("ite",Eqn(Call("Prod.fst",c),D(0)),a,b))),sign))));
    }
    private static Formula ActionStatement()
    {
        var v=F.Id("v"); var m=F.Id("M");
        return All("v",Row(),All("M",Matrix(),Eqn(At(Local("rowAction"),v,m),
            Call("WithLp.toLp",D(2),Call("Matrix.vecMul",Call("WithLp.ofLp",v),m)))));
    }
    private static Formula WordStatement()
    {
        var r=F.Id("rho"); var k=F.Id("k"); var w=F.Id("w");
        var empty=All("w",Words(D(0)),Eqn(At(Local("word"),r,D(0),w),Typed(D(1),Matrix())));
        var next=All("k",Nat(),All("w",Words(Add(k,D(1))),Eqn(At(Local("word"),r,Add(k,D(1)),w),
            Mul(At(Local("word"),r,k,Call("Fin.init",w)),At(Local("letter"),r,At(w,Call("Fin.last",k)))))));
        return All("rho",Real(),And(empty,next));
    }
    private static Formula AverageStatement()
    {
        var r=F.Id("rho"); var k=F.Id("k"); var v=F.Id("v"); var w=F.Id("w");
        return All("rho",Real(),All("k",Nat(),All("v",Row(),Eqn(Avg(r,k,v),
            Mul(Pow(Div(D(1),D(4)),k),SumOver("w",Words(k),Norm(At(Local("rowAction"),v,At(Local("word"),r,k,w)))))))));
    }
    private static Formula FactorStatement()
    {
        var r=F.Id("rho");
        return All("rho",Real(),Eqn(Factor(r),Sub(Root(r),Div(Mul(Pow(r,D(2)),Pow(Sub(D(1),r),D(2))),Mul(D(2),Pow(Add(D(1),Mul(D(3),r)),D(3)))))));
    }
    private static Formula GrowthStatement()
    {
        var r=F.Id("rho"); var k=F.Id("k"); var v=F.Id("v");
        var conclusion=And(Lt(D(0),Factor(r)),And(Lt(Factor(r),Root(r)),And(Lt(Root(r),D(2)),And(Lt(D(1),Factor(r)),Le(Avg(r,k,v),Mul(Pow(Factor(r),k),Norm(v)))))));
        return All("rho",Real(),Imp(Lt(D(0),r),Imp(Lt(r,D(1)),All("k",Nat(),All("v",Row(),conclusion)))));
    }
}
