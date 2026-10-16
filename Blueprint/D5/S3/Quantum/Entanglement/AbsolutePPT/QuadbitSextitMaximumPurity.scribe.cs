using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitSextitMaximumPurityDocument : IScribeDocumentDefinition
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
    private static readonly LibraryNoteRef Hildebrand =
        LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra");
    private static readonly LibraryNoteRef Tran =
        LibraryNoteRef.Create("D5/L/QuantumStates/tran2026spectralappt");
    private static Formula rho => Id("rho");
    private static Formula J => Prod(Fin(Int(4)),Fin(Int(6)));
    private static Formula StateType => Matrix(J,J,C);
    private static Formula Purity => MemberCall("Complex","re",Trace(Mul(rho,rho)));
    private static Formula Maximum => Frac(Int(8),Int(169));
    private static Formula Density => And(Positive(rho),Eq(Trace(rho),Int(1)));
    private static Formula PrescribedState()
    {
        var ij=Id("ij");
        var pair=Parenthesized(Seq(Int(0),Comma,Int(0)));
        var entries=Seq(Id("if"),Sp,Parenthesized(Eq(ij,pair)),Sp,Id("then"),Sp,
            Parenthesized(Seq(Frac(Int(3),Int(26)),Colon,C)),Sp,Id("else"),Sp,
            Parenthesized(Seq(Frac(Int(1),Int(26)),Colon,C)));
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
        string prose, DescribeRole role=DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("appt-quadbit-sextit-maximum-purity-"+name),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSextitMaximumPurity."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Hildebrand,Source,Tran),Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The known 4-by-6 APPT purity maximum 8/169, attained by (3/26,1/26,...,1/26), is an application of the generic finite Bell-corner formal mechanism.",
        H("Exact quadbit–sextit APPT maximum purity"),Blocks(
            Desc("claim","Upper bound, supremum and explicit attaining state",ClaimDefinition(),
                "Ahiable–Kothakonda–Winter, arXiv:2608.03390v2, Conjecture 6.7, page 29, conjectures that the inscribed absolute-PPT polytope has the same maximum purity as the full APPT set, attained at the spectra in Eq. (44). The displayed claim is the m=4, n=6 application: rho is a complex matrix on Fin 4 × Fin 6, positive semidefinite with trace one, and APPT means the second-factor partial transpose of U rho Uᴴ is positive semidefinite for every global unitary U. Purity is the real part of trace(rho*rho). It asserts the universal upper bound, equality of the real supremum with 8/169, and a density matrix equal to the prescribed diagonal state, with one complex diagonal entry 3/26 and twenty-three entries 1/26. Hildebrand, quant-ph/0502170, Theorem 2 on PDF page 5, gives APPT 4×6→3×8 at total dimension 24 because the minimum local dimension decreases from four to three. Unitary identification preserves trace and purity. The established qutrit maximum and known attaining ray already imply the scalar value. Issue 17734 is research history, not novelty authority. This application adds no independent open-problem count and does not classify all maximizers, address other local dimensions, or equate APPT with absolute separability."),
            Desc("result","Exact maximum in the 4-by-6 sector",Id("claim"),
                "FiniteBellCorner.spectral_reduction produces both necessary rank-three boundary matrices on the largest three and smallest six entries of the decreasing twenty-four-dimensional spectrum. Its boundary selector equals QutritSpectralReduction.boundaryValues 5, so QutritN8PurityBound.certificate_bound gives 32/26²=8/169. This direct Lean proof uses the product-corner construction instead of formalizing the fixed-total-dimension monotonicity theorem as a new prerequisite. For the computational basis vector psi, the state (I+2|psi><psi|)/26 has trace one and purity (24+8)/26². After every global unitary its unscaled matrix belongs to the separable cone by LowRankRays.separableCone_one_add_two_rankOne; second-factor partial transpose preserves positivity of each separable product term. The diagonal entries are exactly 3/26 at (0,0) and 1/26 elsewhere. The upper bound and this witness give the real supremum. Against immutable baseline 8a32282e7f57c3a751640623624ee9d1ac5b3a25, result is content under escape-witness: unfolding density_bound and the same-delivery FiniteBellCorner.spectral_reduction leaves the new product-corner necessity inference on the live path to the universal upper bound and supremum. The baseline qutrit reduction does not instantiate to a 4-by-6 product. The scalar value is known mathematically; admission rests on the new formal inference, not an open-problem exception. The attainment helpers are bind-only and consumed by result. Utility is none: the delivered inference concerns arbitrary complex densities and all global unitaries; it introduces no enumeration, checker, numerical premise or finite certificate instance. The already-frozen rational certificate is reused, and evaluating the explicit ray is helper normalization. This application establishes no maximizer classification or priority claim.",
                DescribeRole.Theorem))));
}
