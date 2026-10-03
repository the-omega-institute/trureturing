using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ModularDivisorWeightResolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ModularDivisorWeightResolution.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For each fixed real C>1, on a factorial congruence domain with height (m!)^C, the largest relative divisor-weight response has a sharp logarithmic rate. The same congruent pair has a diverging additive gap.",
        H("Sharp Factorial Divisor Weight Resolution"), Blocks(
            Definition("prime-interval", "Prime interval", "blockSet", IntervalFormula(),
                "S(m,x) is the finite set of primes p with m < p <= floor(x), where the floor takes values in the naturals and is zero for negative x."),
            Definition("prime-block", "Prime block", "primeBlock", BlockFormula(),
                "Q(m,x) multiplies every prime in S(m,x) once; an empty product is one."),
            Definition("lower-cutoff", "Lower cutoff", "lowerCutoff", CutoffFormula(),
                "Y(C,m)=((C-1)/8)*m*log(m). The logarithm is the real logarithm."),
            Definition("factorial-prime-number", "Factorial prime-block number", "lowerNumber", NumberFormula(),
                "A(C,m)=m!*Q(m,Y(C,m)). Thus A(C,m) and m! have the same zero residue modulo m!."),
            Definition("ratio-domain", "Actual ratio domain", "pairValues", ValuesFormula(),
                "V(C,m) consists of Z(a)/Z(b) for positive natural integers a,b at most (m!)^C and congruent modulo m!. Here Z(n)=sigma(n)/n and sigma sums the positive divisors. This is one common height and congruence domain."),
            Definition("extreme-ratio", "Extreme ratio", "extremeRatio", ExtremeFormula(),
                "E(C,m) is the real supremum of V(C,m); the supremum of an empty admissible set is zero. For C>1 the theorem shows that V is finite, contains one, and contains E, so this supremum is an actual maximum."),
            Describe.Lean(DescribeId.Create("sharp-factorial-resolution"), DeclarationHandle.Create(Prefix+"result"),
                H("Sharp relative rate and additive divergence"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Fix any real C>1. For every natural m, the set V(C,m) is finite, contains one, and contains its maximum E(C,m), which is at least one. For all sufficiently large m, A(C,m) is positive, both A(C,m) and m! are at most (m!)^C, they are congruent modulo m!, and Q(m,Y(C,m)) is coprime to m!. The normalized divisor-weight quotient Z(A(C,m))/Z(m!) is the product of 1+1/p on S(m,Y(C,m)). Both the maximum relative excess and this pair's relative excess, multiplied by log(m)/log(log(m)), tend to one. For this same pair the additive gap divided by exp(gamma)*log(log(m)) tends to one, and the additive gap tends to positive infinity. Here gamma is the Euler--Mascheroni constant."))), DescribeRole.Theorem),
            Paragraph(Text("For the upper estimate, split the prime factors at X=m*log(m)*log(log(m)). The factorial-congruence squeeze bounds the small factors. The complete Euler product on m<p<=X and the logarithmic tail bound give the matching upper rate. Mertens' logarithmic error estimate controls the interval product at this scale.")),
            Paragraph(Text("For the lower estimate, take the actual pair A(C,m),m! with cutoff Y(C,m). The primorial bound and the logarithmic factorial lower bound place both integers in the prescribed height domain. Coprimality gives the product of 1+1/p exactly. Factoring it as the interval Euler product times the product of 1-1/p^2 leaves a correction between 1-1/m and one. This gives the matching lower rate. The logarithms of this pair's ratio and the maximum tend to zero, so exponentiation preserves the first-order excess.")),
            Paragraph(Text("Finally Z(m!)/(exp(gamma)*log(m)) tends to one. Multiplication with the pair's relative excess gives the additive asymptotic. Uniform convergence of relative responses therefore does not imply that additive gaps vanish. This conclusion supplies no Robin inequality violation.")) )));

    private static DocumentBlock Definition(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix+name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname,Grp(F.Id(name))),[..args]);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Sub(Formula a, Formula b) => Seq(a,Minus,b);
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => Seq(a,Caret,Grp(b));
    private static Formula N => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula All(Formula a, Formula t, Formula body) => Seq(Forall,Sp,a,InMacro,Sp,t,Comma,Sp,body);
    private static Formula m => F.Id("m");
    private static Formula c => F.Id("C");
    private static Formula x => F.Id("x");
    private static Formula p => F.Id("p");
    private static Formula Fac => Seq(m,Bang);
    private static Formula Y => Call("Y",c,m);
    private static Formula A => Call("A",c,m);
    private static Formula B => Call("Q",m,Y);
    private static Formula V => Call("V",c,m);
    private static Formula E => Call("E",c,m);
    private static Formula Z(Formula a) => Call("Z",a);
    private static Formula L => Call("log",m);
    private static Formula LL => Call("log",L);
    private static Formula Ratio => Fr(Z(A),Z(Fac));
    private static Formula Gap => Sub(Z(A),Z(Fac));
    private static Formula Limit(Formula f, Formula v) => Equal(Seq(new Formula.Subscript(Lim,Seq(m,To,Infty)),f),v);
    private static Formula IntervalFormula() => Disp(All(m,N,All(x,R,Equal(Call("S",m,x),
        Seq(OpenBrace,p,InMacro,Sp,N,Mid,Sp,Call("Prime",p),Land,Sp,m,Lt,p,Le,Sp,new Formula.Floor(Seq(Sp,x)),CloseBrace)))));
    private static Formula BlockFormula() => Disp(All(m,N,All(x,R,Equal(Call("Q",m,x),
        Seq(new Formula.Subscript(Prod,Seq(p,InMacro,Sp,Call("S",m,x))),p)))));
    private static Formula CutoffFormula() => Disp(All(c,R,All(m,N,Equal(Y,Seq(Fr(Sub(c,D(1)),D(8)),m,L)))));
    private static Formula NumberFormula() => Disp(All(c,R,All(m,N,Equal(A,Seq(Fac,B)))));
    private static Formula ValuesFormula()
    {
        var a=F.Id("a"); var b=F.Id("b");
        return Disp(All(c,R,All(m,N,Equal(V,Seq(OpenBrace,Fr(Z(a),Z(b)),Mid,Sp,
            a,Comma,b,InMacro,Sp,N,Comma,D(1),Le,Sp,a,Comma,b,Le,Sp,Pow(Par(Fac),c),Comma,
            a,Equiv,Sp,b,Pmod,Grp(Fac),CloseBrace)))));
    }
    private static Formula ExtremeFormula() => Disp(All(c,R,All(m,N,Equal(E,Call("sup",V)))));
    private static Formula ResultFormula()
    {
        var threshold=F.Id("M");
        var maximum=All(m,N,Seq(Call("Finite",V),Land,Sp,D(1),InMacro,Sp,V,Land,Sp,E,InMacro,Sp,V,Land,Sp,D(1),Le,Sp,E));
        var construction=Seq(Exists,Sp,threshold,InMacro,Sp,N,Comma,Sp,All(m,N,Seq(threshold,Le,Sp,m,Rightarrow,Sp,
            D(0),Lt,A,Land,Sp,A,Le,Sp,Pow(Par(Fac),c),Land,Sp,Fac,Le,Sp,Pow(Par(Fac),c),Land,Sp,
            A,Equiv,Sp,Fac,Pmod,Grp(Fac),Land,Sp,Equal(Call("gcd",Fac,B),D(1)),Land,Sp,
            Equal(Ratio,Seq(new Formula.Subscript(Prod,Seq(p,InMacro,Sp,Call("S",m,Y))),Par(Seq(D(1),Plus,Fr(D(1),p))))))));
        return Disp(All(c,R,Seq(D(1),Lt,c,Rightarrow,Sp,
            Par(maximum),Land,Sp,Par(construction),Land,Sp,
            Limit(Seq(Par(Sub(E,D(1))),Fr(L,LL)),D(1)),Land,Sp,
            Limit(Seq(Par(Sub(Ratio,D(1))),Fr(L,LL)),D(1)),Land,Sp,
            Limit(Fr(Gap,Seq(Call("exp",GammaLower),LL)),D(1)),Land,Sp,
            Limit(Gap,Infty))));
    }
}
