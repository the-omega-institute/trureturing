using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class AbedNikolaevaNovikovAFDensityBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/abednikolaevanovikov2026traces");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Alhasan–Fawwaz quotient is bounded by dimension independently of every positive definite density.",
        H("Density-independent boundedness in fixed dimension"),
        Blocks(
            Entry("quotient-values", "quotientValues", "The original quotient set", QuotientDefinition(),
                "For an arbitrary finite index type iota, bornProbability(rho,Y) is the existing unnormalized complex trace Tr(rho Y). "
                + "The set consists exactly of real q obtained from A positive semidefinite, B Hermitian, and A+iB nonzero. "
                + "Both traces are projected to their real parts. Positivity of rho makes the denominator strictly positive. "
                + "The definition is Section 5.12 of arXiv:2610.34388v1, with the standing positive definite density convention of Section 3.1.",
                DescribeRole.Definition),
            Entry("supremum", "a", "The real supremum", IndexBinders(All("rho", Mat(Id("iota")),
                Eqn(Call("a",Id("rho")),Call("sSup",Call("quotientValues",Id("rho")))))),
                "The real supremum uses the same set, with no trace-one premise. The result proves nonemptiness and an upper bound before applying real completeness; no totalized empty supremum is used.",
                DescribeRole.Definition),
            Entry("accretive-bound", "accretive_le_card_abs", "The matrix inequality", CoreStatement(),
                "For every finite index type and all A positive semidefinite and B Hermitian, A is at most card(iota) times the actual CFC modulus of A+iB in Loewner order. "
                + "Diagonalize P=|A+iB|, rather than A+iB. If P e_j=s_j e_j in an orthonormal basis, then s_j is nonnegative and the square identity gives norm(X e_j)=s_j. "
                + "The real part of the quadratic form of X is that of A, so Cauchy–Schwarz gives h_j=inner(e_j,A e_j) at most s_j. "
                + "For Q=sqrt(A), expand any v in the same basis. Triangle inequality and finite Cauchy–Schwarz bound norm(Q v) squared by card(iota) times the sum of norm(z_j) squared h_j, "
                + "and hence by card(iota) times inner(v,P v). Zero eigenvalues and the zero-dimensional case remain included; no singular value is inverted.",
                DescribeRole.Theorem),
            Entry("claim", "claim", "The original boundedness question", ResultStatement(),
                "For every positive dimension there exists one finite real bound before the quantifier over positive definite densities. The quotient set must be nonempty and its real supremum must be a least upper bound.", DescribeRole.Definition),
            Entry("density-bound", "result", "The complete fixed-dimension boundedness assertion", ResultStatement(),
                "This answers the selected sentence of Section 11.2(5), original owner #22774: “Is a bounded on M_n(C) independently of rho?” "
                + "For each natural n at least one, the real witness C equals n and is nonnegative. For every positive definite rho, the proof establishes that every admissible denominator is strictly positive, "
                + "one belongs to the exact quotient set, every quotient lies between zero and C, a(rho) is the actual least upper bound, and 1 is at most a(rho), which is at most C. "
                + "Trace pairing with a PSD matrix is nonnegative by the reused RHLinalg theorem. For strict positivity, factor rho=Y*Y with Y invertible and P=Q squared; "
                + "cyclicity identifies Tr(rho P) with Tr((YQ)*(YQ)). Vanishing forces Q=0 and P=0. Since X is nonzero, its actual modulus is nonzero. "
                + "The identity A=I, B=0 gives one. Nonempty bounded real sets have a genuine least upper bound. "
                + "The density need not have trace one; its condition number never appears. Singular X, n=1 and arbitrary positive density scales are covered. "
                + "The source's dimension-two result, condition-dependent estimates and separate sharpness or factor questions are not claimed as new consequences. Worldwide novelty and the original Alhasan–Fawwaz article remain unverified.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("abed-nikolaeva-novikov-2026-af-density-bound"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string text, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))),role,resolution);

    private static Formula QuotientDefinition()
    {
        var rho=Id("rho"); var q=Id("q"); var aa=Id("A"); var bb=Id("B"); var t=Id("iota");
        return IndexBinders(All("rho",Mat(t),All("q",RealType(),Seq(
            Member(q,Call("quotientValues",rho)),Sp,Iff,Sp,
            Ex("A",Mat(t),Ex("B",Mat(t),Conj(Call("PosSemidef",aa),Call("IsHermitian",bb),
                Neqn(X(aa,bb),D(0)),Eqn(q,new Formula.Fraction(Weight(rho,aa),Weight(rho,Mod(X(aa,bb))))))))))));
    }
    private static Formula CoreStatement()
    {
        var t=Id("iota"); var aa=Id("A"); var bb=Id("B");
        return All("iota",Id("Type"),Seq(OpenBracket,Call("Fintype",t),CloseBracket,Sp,
            OpenBracket,Call("DecidableEq",t),CloseBracket,Sp,
            All("A",Mat(t),All("B",Mat(t),Implies(Conj(Call("PosSemidef",aa),Call("IsHermitian",bb)),
                Leq(aa,Mul(Call("card",t),Mod(X(aa,bb)))))))));
    }
    private static Formula ResultStatement()
    {
        var n=Id("n"); var c=Id("C"); var rho=Id("rho");
        var t=Call("Fin",n); var set=Call("quotientValues",rho); var ar=Call("a",rho);
        return All("n",Seq(Mathbb,Grp(Id("N"))),Implies(Leq(D(1),n),Ex("C",RealType(),
            Conj(Leq(D(0),c),All("rho",Mat(t),Implies(Call("PosDef",rho),
                Conj(Call("Nonempty",set),Call("IsLUB",set,ar),Leq(ar,c))))))));
    }
    private static Formula Id(string s) => F.Id(s);
    private static Formula IndexBinders(Formula body) => All("iota",Id("Type"),Seq(
        OpenBracket,Call("Fintype",Id("iota")),CloseBracket,Sp,
        OpenBracket,Call("DecidableEq",Id("iota")),CloseBracket,Sp,body));
    private static Formula Mat(Formula t) => Call("Matrix",t,t,Seq(Mathbb,Grp(Id("C"))));
    private static Formula RealType() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Weight(Formula r,Formula y) => Seq(Re,Open,Call("Tr",Mul(r,y)),Close);
    private static Formula X(Formula a,Formula b) => Seq(Open,a,Sp,Plus,Sp,Mul(Id("i"),b),Close);
    private static Formula Mod(Formula x) => Call("abs",x);
    private static Formula Mul(Formula a,Formula b) => Seq(a,Sp,b);
    private static Formula Eqn(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Neqn(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Leq(Formula a,Formula b) => Seq(a,Sp,Le,Sp,b);
    private static Formula Member(Formula a,Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula All(string x,Formula t,Formula b) => Seq(Open,Forall,Sp,Id(x),Colon,Sp,t,Comma,Sp,b,Close);
    private static Formula Ex(string x,Formula t,Formula b) => Seq(Open,Exists,Sp,Id(x),Colon,Sp,t,Comma,Sp,b,Close);
    private static Formula Implies(Formula a,Formula b) => Seq(Open,a,Sp,Rightarrow,Sp,b,Close);
    private static Formula Conj(params Formula[] p)
    {
        var r=p[p.Length-1];
        for(var k=p.Length-2;k>=0;k--) r=Seq(Open,p[k],Sp,Land,Sp,r,Close);
        return r;
    }
    private static Formula Call(string n,params Formula[] a)
    {
        var p=new System.Collections.Generic.List<Formula>{Id(n),Open};
        for(var k=0;k<a.Length;k++){if(k>0){p.Add(Comma);p.Add(Sp);}p.Add(a[k]);}
        p.Add(Close); return Seq(p.ToArray());
    }
}
