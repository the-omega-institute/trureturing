using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitMaximumPurityDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Id(name),[..xs]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall,Sp,Parenthesized(Seq(Id(name),Colon,type)),Comma,Sp,body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p),Rightarrow,Sp,q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) =>
        i == 0 ? new[] {Parenthesized(f)} : new[] {Land,Sp,Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x,F.Eq,y);
    private static Formula Le(Formula x, Formula y) => Seq(x,Leq,Sp,y);
    private static Formula Mul(Formula x, Formula y) => Seq(x,Cdot,Sp,y);
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x,y);
    private static Formula Fin(Formula d) => Call("Fin",d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x,Times,Sp,y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix",i,j,field);
    private static Formula Qualified(string owner, string member) => Seq(Id(owner),Dot,Id(member));
    private static Formula MemberCall(string owner, string member, params Formula[] xs) =>
        new Formula.Apply(Qualified(owner,member),[..xs]);
    private static Formula Trace(Formula m) => MemberCall("Matrix","trace",m);
    private static Formula Positive(Formula m) => MemberCall("Matrix","PosSemidef",m);
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry");
    private static readonly LibraryNoteRef Tran =
        LibraryNoteRef.Create("D5/L/QuantumStates/tran2026spectralappt");
    private static Formula rho => Id("rho");
    private static Formula J => Prod(Fin(Int(4)),Fin(Int(4)));
    private static Formula StateType => Matrix(J,J,C);
    private static Formula Purity => MemberCall("Complex","re",Trace(Mul(rho,rho)));
    private static Formula Maximum => Frac(Int(2),Int(27));
    private static Formula Density => And(Positive(rho),Eq(Trace(rho),Int(1)));
    private static Formula PrescribedState()
    {
        var ij=Id("ij");
        var pair=Parenthesized(Seq(Int(0),Comma,Int(0)));
        var entries=Seq(Id("if"),Sp,Parenthesized(Eq(ij,pair)),Sp,Id("then"),Sp,
            Parenthesized(Seq(Frac(Int(1),Int(6)),Colon,C)),Sp,Id("else"),Sp,
            Parenthesized(Seq(Frac(Int(1),Int(18)),Colon,C)));
        var lambda=Seq(Id("fun"),Sp,Parenthesized(Seq(ij,Colon,J)),Sp,Mapsto,Sp,entries);
        return MemberCall("Matrix","diagonal",Parenthesized(lambda));
    }
    private static Formula ExistsState(Formula value, bool prescribed=false)
    {
        var state=And(Density,Call("APPT",rho),Eq(Purity,value));
        var body=prescribed ? And(Eq(rho,PrescribedState()),state) : state;
        return Seq(Exists,Sp,Parenthesized(Seq(rho,Colon,StateType)),Comma,Sp,body);
    }
    private static Formula ClaimDefinition()
    {
        var p=Id("p");
        var set=Seq(OpenBrace,p,Colon,R,Sp,Bar,Sp,ExistsState(p),CloseBrace);
        var bound=All("rho",StateType,Imp(And(Density,Call("APPT",rho)),Le(Purity,Maximum)));
        return Seq(Id("claim"),Iff,Sp,And(bound,
            Eq(Call("sSup",set),Maximum),ExistsState(Maximum,true)));
    }
    private static DocumentBlock Desc(string name, string title, Formula formula,
        string prose, DescribeRole role=DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution=null) =>
        Describe.Lean(DescribeId.Create("appt-quadbit-maximum-purity-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitMaximumPurity."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source,Tran),Blocks(Paragraph(Text(prose))),role,resolution);

    private static Formula NormStatement()
    {
        var v=Id("v"); var i=Id("i");
        var dot=Call("dotProduct",Call("star",v),v);
        var norm=Seq(new Formula.Subscript(F.Sum,Seq(i,Colon,Id("I"))),Sp,
            new Formula.Power(Call("norm",Call("v",i)),Int(2)));
        return All("I",Id("Type"),Seq(OpenBracket,Call("Fintype",Id("I")),CloseBracket,Sp,
            All("v",Seq(Id("I"),To,Sp,C),Imp(Eq(dot,Int(1)),Eq(norm,Int(1))))));
    }
    private static Formula SeparableTransposeStatement()
    {
        var j=Prod(Fin(Id("m")),Fin(Id("n"))); var w=Id("W");
        return All("m",Id("Nat"),All("n",Id("Nat"),All("W",Matrix(j,j,C),
            Imp(Call("separableCone",w),Positive(Call("partialTranspose",w))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal 4-by-4 APPT purity maximum is 2/27 and is attained by the explicit diagonal spectrum (1/6,1/18,...,1/18).",
        H("Exact quadbit–quadbit APPT maximum purity"),Blocks(
            Desc("norm_of_dot_eq_one","Unit dot product gives real squared norm one",NormStatement(),
                "For every finite index type I and complex vector v, star v dot v = 1 implies that the sum of squared coordinate norms is the real number one. This converts unitary preservation of the complex dot product to the normalization used by the separable rank-one ray.",DescribeRole.Theorem),
            Desc("separableCone_partialTranspose_posSemidef","Separable matrices have positive partial transpose",SeparableTransposeStatement(),
                "For all natural local dimensions, second-factor partial transpose preserves positivity of a matrix in the separable cone. Each product of two positive matrices becomes the Kronecker product of the first factor and the transpose of the second, both positive; finite sums preserve positivity.",DescribeRole.Theorem),
            Desc("claim","Upper bound, supremum and explicit attaining state",ClaimDefinition(),
                "Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29, conjectures that the inscribed absolute-PPT polytope has the same maximum purity as the full APPT set, attained at the spectra in Eq. (44). This claim is precisely its m=n=4 sector: rho is a complex matrix on Fin 4 × Fin 4, positive semidefinite with trace one, and APPT means the second-factor partial transpose of U rho Uᴴ is positive semidefinite for every global unitary U. Purity is the real part of trace(rho*rho). It asserts the universal upper bound, equality of the real supremum with 2/27, and a density matrix equal to the prescribed diagonal state, with one complex diagonal entry 1/6 and fifteen entries 1/18. It does not classify all maximizers, address other local dimensions, or equate APPT with absolute separability."),
            Desc("result","Exact maximum in the 4-by-4 sector",Id("claim"),
                "The proof derives necessary rank-three Bell-corner matrices from the literal APPT predicate. With t the tenth decreasing eigenvalue, positivity gives t≤1/13. Inserting two copies of t for t≤1/18, or deleting t for t≥1/18, preserves both boundary matrices after positive normalization. The original dimension-18 and dimension-15 sharp spectral certificates then give the upper bound 2/27. These are reused certificate theorems, with no copied certificates and no assumption of Hildebrand sufficiency in local dimension four. The known low-rank separable ray proves APPT for the explicit attaining state. This resolves only the stated 4-by-4 sector; worldwide priority remains outside the formal theorem.",
                DescribeRole.Theorem,new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ahiable-kothakonda-winter-2026-appt-quadbit-maximum-purity"),
                    ResolutionKind.Proved)))));
}
