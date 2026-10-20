using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal sealed class MonicAnnihilatorStirlingTransformDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/BinomialBases/MonicAnnihilatorStirlingTransform.";
    private static readonly LibraryNoteRef Sources = LibraryNoteRef.Create("D5/L/Recurrence/parisse2024hypersequences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monic Newton connection coefficients give factorial-row reflections and finite transforms of arbitrary complex sequences with a positive-order monic annihilator.",
        H("Newton connections and monic annihilators"),
        Blocks(
            Describe.Lean(DescribeId.Create("newton-polynomials"), DeclarationHandle.Create(Owner + "newton"),
                H("Monic Newton polynomials"), StatementSource.FromAuthor(NewtonDefinition()),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("This recursion is the finite product of X-a-bi for i=0 through n-1. The generalized connection and inverse-basis conventions are classical; the Maier and Mansour-Schork-Shattuck locators are given in the cited note and below. No priority claim is made for them."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("connection-rows"), DeclarationHandle.Create(Owner + "connectionRow"),
                H("Connection rows"), StatementSource.FromAuthor(RowDefinition(false)),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("F denotes connectionRow. Its coefficient recurrence is valid for every complex parameter."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("connection-coefficients"), DeclarationHandle.Create(Owner + "S"),
                H("Connection coefficients"), StatementSource.FromAuthor(CoefficientDefinition("S")),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("S is the coefficient of X to m in the connection row F."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("factorial-rows"), DeclarationHandle.Create(Owner + "G"),
                H("Factorial rows"), StatementSource.FromAuthor(RowDefinition(true)),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("The coefficient of X to m is m! S(alpha,b,a,n,m); all coefficients above degree n vanish."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("newton-power-coefficients"), DeclarationHandle.Create(Owner + "R"),
                H("Newton-to-power coefficients"), StatementSource.FromAuthor(CoefficientDefinition("R")),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("R reads the coefficients of the monic Newton polynomials."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("power-newton-coefficients"), DeclarationHandle.Create(Owner + "T"),
                H("Power-to-Newton coefficients"), StatementSource.FromAuthor(CoefficientDefinition("T")),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("T is the alpha=0 connection family, including b=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("newton-connection"), DeclarationHandle.Create(Owner + "connection"),
                H("The literal Newton expansion"), StatementSource.FromAuthor(Connection()),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("For complex a and b, N(a,b,n) is the product of X-a-bi over 0 <= i < n, with empty product one. The coefficient S(alpha,b,a,n,m) is the coefficient of X to m in F(alpha,b,a,n). Here F at zero is one, and F at n+1 is (X+a-alpha n) F at n plus b X times its derivative. Thus S at row zero is the Kronecker delta, its zero column satisfies S(n+1,0)=(a-alpha n) S(n,0), and its positive columns satisfy S(n+1,m+1)=S(n,m)+(a+b(m+1)-alpha n) S(n,m+1). Entries above the triangle vanish. In particular no truncated predecessor is used at column zero.")),
                    Paragraph(Text("The displayed expansion identifies these recursively constructed coefficients with the monic Newton connection, including coincident nodes b=0. This is Maier's equation (4.8), with his parameters (a,b;r) corresponding to (alpha,b;a) here. Mansour, Schork and Shattuck use S(n,m;alpha,b,a); their convention excludes the all-zero triple, while the monic polynomial definition here includes it. Writing R for the coefficients of N and T=S(0,b,a), the finite connection is the triangular change of basis R(0,alpha) T(a,b). No nonzero parameter is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("newton-basis-inversion"), DeclarationHandle.Create(Owner + "basis_change"),
                H("The finite triangular change of basis"), StatementSource.FromAuthor(BasisChange()),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("R(a,b,n,k) is coeff(N(a,b,n),k) and T(a,b,n,k)=S(0,b,a,n,k). The first two equations give both triangular inverses, with coeff(X to n,k) equal to the Kronecker delta. The last is S(alpha,b;a)=R(0,alpha) T(a,b). Each product is the finite row sum over j=0 through n. Monicity makes the Newton map injective, including when b=0; the displayed equations require no node separation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generalized-row-reflection"), DeclarationHandle.Create(Owner + "reflection"),
                H("Factorial-row reflection"), StatementSource.FromAuthor(Reflection()),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("The row G(alpha,b,a,n) is the sum of m! S(alpha,b,a,n,m) X to m for m=0 through n. Its polynomial differential recurrence is G(n+1)=(a-alpha n+X)G(n)+X(b+X)G'(n). Differentiating the inductive reflection proves the equality for every complex alpha, b and a. The argument uses polynomial operations and also applies at alpha=0, b=0, and their intersections. Maier's equation (4.4) supplies the classical generating-function normalization; the polynomial proof does not divide by alpha or b."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("monic-annihilator-transform"), DeclarationHandle.Create(Owner + "result"),
                H("The full annihilator transform"), StatementSource.FromAuthor(Result()),
                AssessedProvenance.FromRepo(Sources),
                Blocks(Paragraph(Text("For the actual sequence u define L(u,c,f) as the finite sum of coeff(f,j) u(j+c) over the support of f. The recurrence is imposed at every nonnegative index. It implies that L vanishes on every multiple of X to d minus q minus A; it also replaces (q+A) to m by X to dm inside L. Homogenizing the row reflection and substituting Y=q and X=b A proves the displayed identity.")),
                    Paragraph(Text("The source class has d>=1, degree A<d and A(0)=0; A=0 is allowed, including at d=1. All first d values are arbitrary. The bounds on A specify a positive-order monic annihilator; the polynomial argument itself uses the recurrence. All outer sums contain exactly m=0 through ell. Factorials and natural indices are cast to Complex. Every exponent is natural, and exponent zero has value one even when its base is zero. At ell=0 both sides equal u(c). At q=0 the term m=ell remains, with the full pairing of A to ell. At b=0 positive columns are suppressed by b to m, while the Newton family itself remains defined. Zero initial data, repeated roots and every nonnegative offset are included.")),
                    Paragraph(Text("This result concerns the stated generalized-Stirling transform. Inverting Parisse's scaled matrix at a nonzero step, factorial-free first-kind transport, the separate positive Lah companion and arbitrary hypersequence inversion require their own coefficient identifications and hypotheses."))), DescribeRole.Theorem)), []));

    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Cpx() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Poly() => Call("Polynomial", Cpx());
    private static Formula SeqType() => new Formula.TypeArrow(Nats(), Cpx());
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(Par(x), y);
    private static Formula Negate(Formula x) => Sub(D(0), x);
    private static Formula Sum(Formula m, Formula bound, Formula body) => Seq(F.Sum, Underscore, Grp(m, Sp, InMacro, Sp, Call("range", bound)), Sp, Par(body));
    private static Formula Params(Formula body) => All("alpha", Cpx(), All("b", Cpx(), All("a", Cpx(), body)));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x),FormulaLogicOperator.And,Par(y));
    private static Formula NewtonDefinition()
    {
        Formula a=F.Id("a"), b=F.Id("b"), n=F.Id("n");
        return Disp(All("a",Cpx(),All("b",Cpx(),And(Eq(Call("N",a,b,D(0)),D(1)),
            All("n",Nats(),Eq(Call("N",a,b,Add(n,D(1))),
                Mul(Call("N",a,b,n),Sub(F.Id("X"),Call("C",Add(a,Mul(b,n)))))))))));
    }
    private static Formula RowDefinition(bool factorial)
    {
        Formula alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"), n=F.Id("n"), x=F.Id("X");
        string name=factorial ? "G" : "F";
        var row=Call(name,alpha,b,a,n);
        var linear=factorial ? Add(Call("C",Sub(a,Mul(alpha,n))),x) : Add(x,Call("C",Sub(a,Mul(alpha,n))));
        var diff=factorial ? Mul(x,Add(Call("C",b),x)) : Mul(Call("C",b),x);
        return Disp(Params(And(Eq(Call(name,alpha,b,a,D(0)),D(1)),All("n",Nats(),
            Eq(Call(name,alpha,b,a,Add(n,D(1))),Add(Mul(linear,row),Mul(diff,Call("derivative",row))))))));
    }
    private static Formula CoefficientDefinition(string name)
    {
        Formula alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"), n=F.Id("n"), m=F.Id("m");
        if (name=="S") return Disp(Params(All("n",Nats(),All("m",Nats(),
            Eq(Call("S",alpha,b,a,n,m),Call("coeff",Call("F",alpha,b,a,n),m))))));
        Formula body=name=="R" ? Eq(Call("R",a,b,n,m),Call("coeff",Call("N",a,b,n),m))
            : Eq(Call("T",a,b,n,m),Call("S",D(0),b,a,n,m));
        return Disp(All("a",Cpx(),All("b",Cpx(),All("n",Nats(),All("m",Nats(),body)))));
    }
    private static Formula Connection()
    {
        Formula alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"), n=F.Id("n"), m=F.Id("m");
        return Disp(Params(All("n", Nats(), Eq(Call("N", D(0), alpha, n),
            Sum(m, Add(n,D(1)), Mul(Call("C", Call("S",alpha,b,a,n,m)),Call("N",a,b,m)))))));
    }
    private static Formula BasisChange()
    {
        Formula alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"), n=F.Id("n"), k=F.Id("k"), j=F.Id("j");
        var delta=Call("coeff",Pow(F.Id("X"),n),k);
        var first=Eq(Sum(j,Add(n,D(1)),Mul(Call("T",a,b,n,j),Call("R",a,b,j,k))),delta);
        var second=Eq(Sum(j,Add(n,D(1)),Mul(Call("R",a,b,n,j),Call("T",a,b,j,k))),delta);
        var third=Eq(Call("S",alpha,b,a,n,k),Sum(j,Add(n,D(1)),Mul(Call("R",D(0),alpha,n,j),Call("T",a,b,j,k))));
        return Disp(Params(All("n",Nats(),All("k",Nats(),new Formula.Logic(Par(first),FormulaLogicOperator.And,
            Par(new Formula.Logic(Par(second),FormulaLogicOperator.And,Par(third))))))));
    }
    private static Formula Reflection()
    {
        Formula alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"), n=F.Id("n");
        return Disp(Params(All("n", Nats(), Eq(Call("comp",Call("G",alpha,b,a,n),Sub(Negate(Call("C",b)),F.Id("X"))),
            Mul(Call("C",Pow(Negate(D(1)),n)),Call("G",Negate(alpha),b,Sub(b,a),n))))));
    }
    private static Formula Result()
    {
        Formula d=F.Id("d"), q=F.Id("q"), A=F.Id("A"), alpha=F.Id("alpha"), b=F.Id("b"), a=F.Id("a"),
            ell=F.Id("ell"), c=F.Id("c"), u=F.Id("u"), n=F.Id("n"), j=F.Id("j"), m=F.Id("m");
        var recurrence = All("n",Nats(),Eq(Call("u",Add(n,d)),Add(Mul(q,Call("u",n)),
            Seq(F.Sum,Underscore,Grp(j,Sp,InMacro,Sp,Call("support",A)),Sp,Par(Mul(Call("coeff",A,j),Call("u",Add(n,j))))))));
        var left=Sum(m,Add(ell,D(1)),Mul(Mul(Mul(Mul(Mul(Pow(Negate(D(1)),m),Call("factorial",m)),Pow(b,m)),
            Call("S",alpha,b,a,ell,m)),Pow(q,Sub(ell,m))),Call("u",Add(Mul(d,m),c))));
        var right=Mul(Pow(Negate(D(1)),ell),Sum(m,Add(ell,D(1)),Mul(Mul(Mul(Mul(Call("factorial",m),Pow(b,m)),
            Call("S",Negate(alpha),b,Sub(b,a),ell,m)),Pow(q,Sub(ell,m))),Call("L",u,c,Pow(A,m)))));
        return Disp(All("d",Nats(),All("q",Cpx(),All("A",Poly(),Params(All("ell",Nats(),All("c",Nats(),All("u",SeqType(),
            Imp(Le(D(1),d),Imp(Lt(Call("degree",A),d),Imp(Eq(Call("eval",D(0),A),D(0)),Imp(recurrence,Eq(left,right)))))))))))));
    }
}
