using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QuadraticPovmStationarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At an optimum of a finite matrix POVM score, a positive quadratic perturbation of an effect gives an equality between its first-order score and the corresponding weighted total score.",
        H("Stationarity of quadratic POVM variations"),
        Blocks(Describe.Lean(DescribeId.Create("kb-quadratic-stationarity"),
            DeclarationHandle.Create("D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity"),
            H("A first-order necessary condition"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let A and M be families of complex dim by dim matrices indexed by Fin n. Suppose M is a POVM maximizing the sum of the real traces of A(j) M(j). The matrices D and E have real expansions d and e in the effects M(j), and M(i)+t D+t squared E is positive semidefinite for every real t. These hypotheses imply that the real trace of A(i) D equals the d-weighted sum of the real traces of A(j) M(j). No Hermitian assumption on A is required, and both n and dim range over all natural numbers.")),
                Paragraph(Text("Near t=0, the coefficient of M(i) in the perturbed effect stays positive and exceeds each other coefficient. The other effects can therefore be rescaled by positive coefficients so that, after normalization, the family remains a POVM. Optimality bounds its score. Clearing the positive normalization factor yields a real quadratic polynomial with a local maximum at zero. Its linear coefficient vanishes by the derivative condition for a local maximum. This equality supplies the first-order constraints used for the isolated four-state qubit ensemble."))),
            DescribeRole.Theorem)), []));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function,[.. args]);
    private static Formula Qualified(string owner,string name) => Seq(Operatorname,Grp(V(owner),Dot,V(name)));
    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
    private static Formula Field(string name) => Seq(Mathbb,Grp(V(name)));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Mat(Formula dim) => Call("Matrix",Fin(dim),Fin(dim),Field("C"));
    private static Formula Fun(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula All(string name,Formula type,Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Rel(Formula a,FormulaRelationOperator op,Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a,Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Smul(Formula a,Formula b) => App(Qualified("SMul","smul"),a,b);
    private static Formula SumOver(string name,Formula type,Formula value) =>
        Seq(Sum,Underscore,Grp(V(name),Sp,Colon,Sp,type),Sp,Parenthesized(value));
    private static Formula TraceReal(Formula a,Formula b) =>
        Seq(App(Qualified("Matrix","trace"),Mul(a,b)),Dot,V("re"));
    private static Formula Score(Formula n,Formula a,Formula m) =>
        SumOver("j",Fin(n),TraceReal(App(a,V("j")),App(m,V("j"))));

    private static Formula Statement()
    {
        Formula n=V("n"), dim=V("dim"), a=V("A"), m=V("M"), i=V("i"),
            matrixD=V("D"), matrixE=V("E"), d=V("d"), e=V("e"), t=V("t"), f=V("F");
        Formula hopt=All("F",Fun(Fin(n),Mat(dim)),Imp(Call("IsPOVM",f),
            Rel(Score(n,a,f),FormulaRelationOperator.LessThanOrEqual,Score(n,a,m))));
        Formula hd=Eq(SumOver("j",Fin(n),Smul(App(d,V("j")),App(m,V("j")))),matrixD);
        Formula he=Eq(SumOver("j",Fin(n),Smul(App(e,V("j")),App(m,V("j")))),matrixE);
        Formula hcurve=All("t",Field("R"),App(Qualified("Matrix","PosSemidef"),
            Add(Add(App(m,i),Smul(t,matrixD)),Smul(new Formula.Power(t,D(2)),matrixE))));
        Formula conclusion=Eq(TraceReal(App(a,i),matrixD),
            SumOver("j",Fin(n),Mul(App(d,V("j")),TraceReal(App(a,V("j")),App(m,V("j"))))));
        return All("n",Field("N"),All("dim",Field("N"),All("A",Fun(Fin(n),Mat(dim)),
            All("M",Fun(Fin(n),Mat(dim)),All("i",Fin(n),Imp(Call("IsPOVM",m),Imp(hopt,
            All("D",Mat(dim),All("E",Mat(dim),All("d",Fun(Fin(n),Field("R")),
            All("e",Fun(Fin(n),Field("R")),Imp(hd,Imp(he,Imp(hcurve,conclusion))))))))))))));
    }
}
