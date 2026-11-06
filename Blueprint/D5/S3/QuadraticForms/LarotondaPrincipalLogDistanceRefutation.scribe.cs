using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class LarotondaPrincipalLogDistanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/LarotondaPrincipalLogDistanceRefutation.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/QuadraticForms/larotonda2026shortcurves");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula E => Seq(Mathbb, Grp(F.Id("R")), Underscore, Grp(Seq(Geq, Num(0))), Caret, Grp(Infty));
    private static Formula n => F.Id("n");
    private static Formula z => F.Id("z");
    private static Formula f => F.Id("F");
    private static Formula g => F.Id("gamma");
    private static Formula Mat => Call("Matrix", Call("Fin", n), Call("Fin", n), C);
    private static Formula Func(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula a, params Formula[] args) => Seq(a, Parenthesized(Seq(args.SelectMany((x,i) => i == 0 ? new[] {x} : new[] {Comma, Sp, x}).ToArray())));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string v, Formula t, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(v), t)], body);
    private static Formula ExistsF(string v, Formula t, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(v), t)], body);
    private static Formula Skew(Formula x) => Mem(x, Call("skewAdjoint", Mat));
    private static Formula Unit(Formula x) => Mem(x, App(Q("Matrix", "unitaryGroup"), Call("Fin", n), C));
    private static Formula Icc(Formula a, Formula b) => App(Q("Set", "Icc"), a, b);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert, Sp);
    private static Formula OfReal(Formula x) => App(Q("ENNReal", "ofReal"), x);
    private static Formula ExpF(Formula x) => App(Q("NormedSpace", "exp"), x);

    public DocumentDefinition Create()
    {
        Formula x=F.Id("x"), y=F.Id("y"), u=F.Id("u"), v=F.Id("v"), r=F.Id("r"), t=F.Id("t"), m=F.Id("m"), tau=F.Id("tau"), j=F.Id("j"), l=F.Id("L");
        Formula finsler=And(Eq(App(f,Num(0)),Num(0)),
            All("z",Mat,Imp(Skew(z),Le(Num(0),App(f,z)))),
            All("z",Mat,Imp(Skew(z),IffF(Eq(App(f,z),Num(0)),Eq(z,Num(0))))),
            All("x",Mat,All("y",Mat,Imp(Skew(x),Imp(Skew(y),Le(App(f,Add(x,y)),Add(App(f,x),App(f,y))))))),
            All("r",R,All("z",Mat,Imp(Le(Num(0),r),Imp(Skew(z),Eq(App(f,Seq(r,Sp,Cdot,Sp,z)),Multiply(r,App(f,z))))))),
            All("u",Mat,All("z",Mat,Imp(Unit(u),Imp(Skew(z),Eq(App(f,Multiply(Multiply(u,z),Call("star",u))),App(f,z)))))) ,
            All("z",Mat,Imp(Skew(z),Le(Norm(App(Q("Matrix","toEuclideanCLM"),z)),App(f,z)))));
        Formula smooth=And(Call("ContinuousOn",g,Icc(Num(0),Num(1))),
            ExistsF("m",N,ExistsF("tau",Func(Call("Fin",Add(m,Num(1))),R),
                And(Eq(App(tau,Num(0)),Num(0)),Eq(App(tau,App(Q("Fin","last"),m)),Num(1)),
                    Call("StrictMono",tau),All("j",Call("Fin",m),
                        Call("ContDiffOn",R,Infty,g,Icc(App(tau,App(Q("Fin","castSucc"),j)),App(tau,App(Q("Fin","succ"),j)))))))));
        Formula curve=And(Call("PiecewiseSmooth",g),Eq(App(g,Num(0)),u),Eq(App(g,Num(1)),v),
            All("t",R,Imp(Mem(t,Icc(Num(0),Num(1))),Unit(App(g,t)))));
        Formula length=Seq(Int,Underscore,Grp(Seq(t,Sp,Colon,R,Sp,InMacro,Sp,Icc(Num(0),Num(1)))),Caret,Grp(Minus),Sp,
            OfReal(App(f,Multiply(Call("star",App(g,t)),Call("deriv",g,t)))));
        Formula lengths=Seq(OpenBrace,l,Sp,Colon,Sp,E,Sp,Mid,Sp,
            ExistsF("gamma",Func(R,Mat),And(Call("IsCurve",u,v,g),Eq(l,Call("curveLength",f,g)))),CloseBrace);
        return DocumentDefinition.Create(ScribeNode.Create(
            "A winding shift shortens a trace-coupled quadratic norm while preserving a unitary endpoint.",
            H("Ad-invariant principal-log distance: a two-dimensional refutation"),Blocks(
                Item("IsAdInvariantFinsler","Ad-invariant Finsler norm",All("n",N,All("F",Func(Mat,R),IffF(Call("IsAdInvariantFinsler",f),finsler))),
                    "Section 4, p. 5: “Let ‖·‖ be an Ad-invariant Finsler norm on su(n), that is, a subadditive, nondegenerate and positively homogeneous function (‖λv‖=λ‖v‖ for λ≥0) with ‖Adᵤv‖=‖v‖ for u∈SU(n); we do not assume ‖−v‖=‖v‖.” Section 4.1, p. 7 applies this definition to u(n). Matrices outside skewAdjoint impose no restriction. Spectral domination is the normalization of p. 7.",true),
                Item("PiecewiseSmooth","Piecewise smooth curves",All("n",N,All("gamma",Func(R,Mat),IffF(Call("PiecewiseSmooth",g),smooth))),
                    "A continuous curve on Set.Icc 0 1 has a finite strictly increasing partition, and is smooth on every closed subinterval. The partition has m pieces and m+1 endpoints.",true),
                Item("IsCurve","Unitary curves with fixed endpoints",All("n",N,All("u",Mat,All("v",Mat,All("gamma",Func(R,Mat),IffF(Call("IsCurve",u,v,g),curve))))),
                    "The curve starts at u, ends at v, and lies in Matrix.unitaryGroup throughout Set.Icc 0 1.",true),
                Item("curveLength","Left logarithmic length",All("n",N,All("F",Func(Mat,R),All("gamma",Func(R,Mat),Eq(Call("curveLength",f,g),length)))),
                    "Section 2.1, p. 2: “The length of a piecewise smooth curve γ⊂U(n) is L(γ)=∫‖γ⁻¹γ̇‖, and d is the induced rectifiable distance, which is bi-invariant.” On unitary matrices star equals inverse. The integral is the extended nonnegative integral for Lebesgue measure on Set.Icc 0 1; finitely many partition points do not affect it.",true),
                Item("rectifiableDistance","Directed rectifiable distance",All("n",N,All("F",Func(Mat,R),All("u",Mat,All("v",Mat,Eq(Call("rectifiableDistance",f,u,v),Call("sInf",lengths)))))),
                    "Section 4, p. 5: “Throughout, d(u,w) is the distance from u to w: the infimum of L(γ)=∫‖γ⁻¹γ̇‖ over curves γ starting at u and ending at w.” Empty sets of lengths have infimum infinity.",true),
                Item("claim","The conjectured principal-log formula",IffF(F.Id("claim"),ClaimBody()),
                    "After Proposition 4.3, p. 7: “It would be natural to conjecture that d(1,eᶻ)=‖z‖ whenever ‖z‖∞≤π.” Here n ranges over positive natural numbers, F over all normalized Ad-invariant Finsler norms, and z over skewAdjoint matrices. No symmetry, trace-zero condition, or singular-value invariance is imposed.",true),
                Item("result","The universal equality is false",Seq(Neg,Sp,Parenthesized(ClaimBody())),
                    "For F(z)²=Σᵢⱼ‖zᵢⱼ‖²+4‖Matrix.trace z‖², use diagonal angles (4π/5,π/2) and (−6π/5,π/2). Their exponentials agree. The smooth exponential curve for the second vector has constant left logarithmic derivative and strictly smaller length, so the infimum is strictly below F at the first vector.",false))));
    }

    private static Formula ClaimBody() => All("n",N,Imp(new Formula.Relation(Num(0),FormulaRelationOperator.LessThan,n),
        All("F",Func(Mat,R),Imp(Call("IsAdInvariantFinsler",f),All("z",Mat,
            Imp(Skew(z),Imp(Le(Norm(App(Q("Matrix","toEuclideanCLM"),z)),Q("Real","pi")),
                Eq(Call("rectifiableDistance",f,Num(1),ExpF(z)),OfReal(App(f,z))))))))));
    private static DocumentBlock Item(string name,string title,Formula formula,string prose,bool literature) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()),DeclarationHandle.Create(Owner+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),literature ? DescribeRole.Definition : DescribeRole.Theorem);
}
