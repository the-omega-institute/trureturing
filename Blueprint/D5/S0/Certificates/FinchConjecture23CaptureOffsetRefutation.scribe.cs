using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FinchConjecture23CaptureOffsetRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FinchConjecture23CaptureOffsetRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/finch2026quadraticrecurrences");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The k = 2 recurrence has least period 4, least preperiod 0 and least capture endpoint 9.",
        H("Finch Conjecture 23 fails at the purely periodic boundary"),
        Blocks(
            Node("IsSourceSequence", "Recurrence A on positive indices", SourceFormula(),
                "Finch, arXiv:2610.34300v1, pp. 1 and 9, recurrence (A) and the final Addendum. All values lie in ZMod 3. Initial indices satisfy 1 ≤ n < k; x(k)=1; the recurrence applies for n ≥ k+1. Index zero is unconstrained and unused for k ≥ 2."),
            Node("IsEventualPeriod", "Positive eventual periods", PeriodFormula(),
                "Finch, p. 1. A positive period holds after some natural threshold, with the strict inequality n > m."),
            Node("HasLeastEventualPeriod", "The least positive eventual period", LeastPeriodFormula(),
                "IsLeast means membership and a lower bound on every other member. No default minimum is assigned to an empty set."),
            Node("gaps", "The capture gap count", All("k", Nat(), Eq(Call("gaps", V("k")), Call("NatDiv", Add(Sub(V("k"), D(1)), D(3)), D(4)))),
                "Finch, p. 9. For k ≥ 2, this natural-number division equals ceil((k-1)/4). NatDiv denotes floor division, and subtraction here is natural subtraction."),
            Node("IsRun", "A run with g four-spaced gaps", RunFormula(),
                "Finch, Definition 15, p. 6, reused in the final Addendum, p. 9. The start is at least k+1, g is positive, all g+1 listed positions are zero, and every other interior position is nonzero. The run need not be maximal. NatMod is natural remainder."),
            Node("IsCapturePoint", "The least capturing endpoint", CaptureFormula(),
                "Finch, Definition 21, p. 9. An endpoint belongs exactly when a qualifying run with gaps(k) gaps ends there; it is a capture point exactly when it is the least such endpoint."),
            Node("IsPreperiod", "The least four-preperiod", PreperiodFormula(),
                "Finch, Definition 22, p. 9. The least natural m satisfies x(n+4)=x(n) for all n>m. The source's accompanying last-disagreement equivalence needs a separate convention in the purely periodic case; the explicit least-m definition is used here."),
            Node("claim", "Conjecture 23 on the full original domain", Iff(V("claim"), ClaimBody()),
                "Finch, Conjecture 23, p. 9. The domain includes k=2 and preperiod zero. The first conjunct explicitly requires source-sequence existence for each k ≥ 2; the second quantifies every such sequence, requires k mod 4 equal to 2 or 3 and least eventual period 4, and asserts existence of least capture and preperiod indices with integer difference 6."),
            Describe.Lean(DescribeId.Create("finch-capture-offset-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The original universal offset identity is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For k=2 the explicit positive-index sequence repeats (0,1,1,2). A four-residue argument verifies the recurrence at every n≥3. Periods 1, 2 and 3 fail arbitrarily far out, while period 4 holds from the first term, so the least positive eventual period is 4 and the least four-preperiod is 0. Here gaps(2)=1. The run from 5 to 9 has no extra interior zeros; any allowed earlier start would be 3 or 4, whose values are nonzero. Thus the least capture endpoint is 9, and 9-0 is not 6. This is completion of the existing #23615 hand route, without a discovery or priority claim. It proves neither an infinite exceptional family nor a corrected k≥3 or positive-preperiod law."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("finch-2026-conjecture-23-capture-offset"), ResolutionKind.Refuted)))));

    private static Formula SourceFormula()
    {
        var k = V("k"); var x = V("x"); var n = V("n");
        return All("k", Nat(), All("x", Sequence(), Iff(Call("IsSourceSequence", k, x), And(
            All("n", Nat(), Imp(Le(D(1), n), Imp(Lt(n, k), Eq(Call("x", n), D(0))))),
            Eq(Call("x", k), D(1)),
            All("n", Nat(), Imp(Le(Add(k, D(1)), n), Eq(Call("x", n),
                Add(Call("x", Sub(n, D(1))), new Formula.Power(Call("x", Sub(n, k)), D(2)))))))));
    }
    private static Formula PeriodFormula() => All("x", Sequence(), All("p", Nat(),
        Iff(Call("IsEventualPeriod", V("x"), V("p")), And(Lt(D(0), V("p")),
            Ex("m", Nat(), All("n", Nat(), Imp(Lt(V("m"), V("n")),
                Eq(Call("x", Add(V("n"), V("p"))), Call("x", V("n")))))))));
    private static Formula LeastPeriodFormula() => All("x", Sequence(), All("p", Nat(),
        Iff(Call("HasLeastEventualPeriod", V("x"), V("p")), And(
            Call("IsEventualPeriod", V("x"), V("p")), All("q", Nat(),
                Imp(Call("IsEventualPeriod", V("x"), V("q")), Le(V("p"), V("q")))))));
    private static Formula RunFormula()
    {
        var k=V("k"); var x=V("x"); var r=V("r"); var g=V("g"); var n=V("n"); var i=V("i");
        return All("k", Nat(), All("x", Sequence(), All("r", Nat(), All("g", Nat(),
            Iff(Call("IsRun", k,x,r,g), And(Le(Add(k,D(1)),r), Le(D(1),g),
                All("i",Nat(),Imp(Le(i,g),Eq(Call("x",Add(r,Mul(D(4),i))),D(0)))),
                All("n",Nat(),Imp(Lt(r,n),Imp(Lt(n,Add(r,Mul(D(4),g))),
                    Imp(new Formula.Not(Eq(Call("NatMod",Sub(n,r),D(4)),D(0))),new Formula.Not(Eq(Call("x",n),D(0))))))))))));
    }
    private static Formula Endpoint(Formula t) => Ex("r", Nat(), And(
        Call("IsRun",V("k"),V("x"),V("r"),Call("gaps",V("k"))),
        Eq(t,Add(V("r"),Mul(D(4),Call("gaps",V("k")))))));
    private static Formula CaptureFormula() => All("k",Nat(),All("x",Sequence(),All("z",Nat(),
        Iff(Call("IsCapturePoint",V("k"),V("x"),V("z")),And(Endpoint(V("z")),
            All("t",Nat(),Imp(Endpoint(V("t")),Le(V("z"),V("t"))))))));
    private static Formula FourTail(Formula m) => All("n",Nat(),Imp(Lt(m,V("n")),
        Eq(Call("x",Add(V("n"),D(4))),Call("x",V("n")))));
    private static Formula PreperiodFormula() => All("x",Sequence(),All("m",Nat(),
        Iff(Call("IsPreperiod",V("x"),V("m")),And(FourTail(V("m")),
            All("t",Nat(),Imp(FourTail(V("t")),Le(V("m"),V("t")))))));
    private static Formula ClaimBody()
    {
        var k=V("k"); var x=V("x");
        var existence=All("k",Nat(),Imp(Le(D(2),k),Ex("x",Sequence(),Call("IsSourceSequence",k,x))));
        var conclusion=Ex("z",Nat(),Ex("m",Nat(),And(Call("IsCapturePoint",k,x,V("z")),
            Call("IsPreperiod",x,V("m")),Eq(Sub(Cast(V("z")),Cast(V("m"))),D(6)))));
        return And(existence,All("k",Nat(),All("x",Sequence(),Imp(Le(D(2),k),
            Imp(Call("IsSourceSequence",k,x),Imp(Or(Eq(Call("NatMod",k,D(4)),D(2)),Eq(Call("NatMod",k,D(4)),D(3))),
                Imp(Call("HasLeastEventualPeriod",x,D(4)),conclusion)))))));
    }
    private static DocumentBlock Node(string name,string title,Formula formula,string prose) => Describe.Lean(
        DescribeId.Create("finch-capture-offset-"+name.ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
        H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),DescribeRole.Definition);
    private static Formula V(string name)=>F.Id(name);
    private static Formula Nat()=>new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int()=>new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Sequence()=>new Formula.TypeArrow(Nat(),Call("ZMod",D(3)));
    private static Formula Call(string name,params Formula[] args)=>new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula P(Formula x)=>Seq(Open,x,Close);
    private static Formula Cast(Formula x)=>P(Seq(x,Colon,Sp,Int()));
    private static Formula All(string name,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Ex(string name,Formula type,Formula body)=>new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),type,body);
    private static Formula Eq(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Le(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x,Formula y)=>new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Iff(Formula x,Formula y)=>new Formula.Logic(P(x),FormulaLogicOperator.Iff,P(y));
    private static Formula Imp(Formula x,Formula y)=>new Formula.Logic(P(x),FormulaLogicOperator.Implies,P(y));
    private static Formula Or(Formula x,Formula y)=>new Formula.Logic(P(x),FormulaLogicOperator.Or,P(y));
    private static Formula And(params Formula[] xs)
    {
        Formula r=P(xs[^1]);
        for(int i=xs.Length-2;i>=0;i--)r=new Formula.Logic(P(xs[i]),FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Add(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x,Formula y)=>new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
}
