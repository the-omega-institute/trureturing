using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class IsraelA103573RootFloorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/IsraelA103573RootFloor.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/israel2026a103573");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Least integer thresholds for the difference of a square root and a cube root.",
        H("Israel's A103573 ceiling formula"),
        Blocks(
            Node("f", "The root difference", All("x", Real(), Equal(Call("f", F.Id("x")),
                Sub(Call("sqrt", F.Id("x")), Power(F.Id("x"), Div(D(1), D(3))))))),
                "For a nonnegative real argument, sqrt is the nonnegative square root and the real power with exponent 1/3 is the nonnegative cube root.", DescribeRole.Definition),
            Node("T", "The explicit approximation", All("n", Nat(), Equal(Call("T", F.Id("n")), TBody())),
                "All rational coefficients and exponents are real. The approximation is zero at n=0.", DescribeRole.Definition),
            Node("IsSourceSequence", "The source sequence", All("a", SequenceType(),
                Iff(Call("IsSourceSequence", F.Id("a")), SourceBody(F.Id("a"))))),
                "At every natural index n, the sequence takes the least natural k whose ordinary integer floor of sqrt(k)-k^(1/3) is n. The floor is integer valued even when its argument is negative.", DescribeRole.Definition),
            Node("claim", "The full ceiling assertion", Iff(F.Id("claim"), ClaimBody()),
                "The assertion includes existence of the source sequence and applies to every sequence satisfying its leastness definition, at every index including zero.", DescribeRole.Definition),
            Node("result", "Two consecutive ceiling values", F.Id("claim"),
                "For n>0 the polynomial q(t)=t^3-t^2 increases strictly on t>=1 and supplies a threshold r with sqrt(r)-r^(1/3)=n. Put y=n^(1/3) and P_n(X)=X*(X+3*n^2)^2-((3*n+1)*X+n^3)^2. Exact polynomial expansion gives P_n(T(n))<0<P_n(T(n)+1), since the residual factors have positive coefficients. The discarded factor in the square comparison is positive, so these signs imply T(n)<r<T(n)+1. The least admissible integer is ceil(r): its root difference lies in [n,n+1), and all smaller nonnegative integers have root difference below n. Ceiling monotonicity leaves the two stated integer possibilities. At n=0 the least candidate and the approximation are both zero.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("israel-a103573-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula TBody()
    {
        var n = Cast(F.Id("n"), Real());
        return Add(Add(Add(Add(Add(Power(n,D(2)), Mul(D(2),Power(n,Div(D(5),D(3))))),
            Mul(Div(D(7),D(3)),Power(n,Div(D(4),D(3))))),Mul(D(2),n)),
            Mul(Div(D(1,1,0),D(8,1)),Power(n,Div(D(2),D(3))))),
            Mul(Div(D(1,8,2),D(2,4,3)),Power(n,Div(D(1),D(3)))));
    }
    private static Formula SourceBody(Formula a)
    {
        var n=F.Id("n"); var k=F.Id("k");
        var candidates=Seq(OpenBrace,k,Sp,Colon,Sp,Nat(),Sp,Mid,Sp,
            Equal(Floor(Call("f",Cast(k,Real()))),Cast(n,Ints())),CloseBrace);
        return All("n",Nat(),Call("IsLeast",candidates,new Formula.Apply(a,[n])));
    }
    private static Formula ClaimBody()
    {
        var a=F.Id("a"); var n=F.Id("n");
        var an=Cast(new Formula.Apply(a,[n]),Ints());
        var c=Seq(Lceil,Sp,Call("T",n),Sp,Rceil);
        return And(new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create("a"),SequenceType(),Call("IsSourceSequence",a)),
            All("a",SequenceType(),Implies(Call("IsSourceSequence",a),All("n",Nat(),
                new Formula.Logic(Equal(an,c),FormulaLogicOperator.Or,Equal(an,Add(c,D(1))))))));
    }
    private static Formula Nat()=>new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Real()=>new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula Ints()=>new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula SequenceType()=>Seq(Open,Nat(),Sp,To,Sp,Nat(),Close);
    private static Formula All(string name,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Call(string name,params Formula[] args)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula Cast(Formula x,Formula type)=>Seq(Open,x,Sp,Colon,Sp,type,Close);
    private static Formula Floor(Formula x)=>Seq(Lfloor,Sp,x,Sp,Rfloor);
    private static Formula Power(Formula x,Formula y)=>new Formula.Power(x,y);
    private static Formula Div(Formula x,Formula y)=>new Formula.Fraction(x,y);
    private static Formula Add(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Equal(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula And(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula Iff(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Iff,y);
    private static Formula Implies(Formula x,Formula y)=>new Formula.Logic(x,FormulaLogicOperator.Implies,y);
}
