using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritExtremeSixLevelsDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(Num(-n)) : Num(n);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((p,i) => i == 0 ? new[] {Id(p)} : new[] {Dot,Id(p)}).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [..xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i)=> i==0 ? new[] {Parenthesized(f)} : new[] {Land,Sp,Parenthesized(f)}).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Rightarrow,Sp,Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a,F.Eq,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,Sp,b);
    private static Formula Prod(Formula a, Formula b) => Parenthesized(Seq(a,Times,Sp,b));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Mat(Formula i, Formula f) => Call("Matrix",i,i,f);
    private static Formula Ps(Formula a) => Seq(Parenthesized(a),Dot,Id("PosSemidef"));
    private static Formula Tr(Formula a) => Seq(Parenthesized(a),Dot,Id("trace"));
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a,Colon,t));
    private static Formula Card(Formula s) => Seq(Parenthesized(s),Dot,Id("ncard"));
    private static Formula In(Formula a,Formula s) => Seq(a,InMacro,Sp,s);
    private static Formula States => Seq(OpenBrace,Id("rho"),Mid,Sp,And(Ps(Id("rho")),Eq(Tr(Id("rho")),Int(1)),Call("APPT",Id("rho"))),CloseBrace);
    private static Formula J => Prod(Fin(Int(3)),Fin(Int(3)));
    private static Formula M => Mat(J,C);
    private static DocumentBlock Desc(string name,string title,Formula f,string prose,DescribeRole role=DescribeRole.Theorem,AssessedProvenance? p=null,OpenProblemResolutionClaim? resolution=null) => Describe.Lean(
        DescribeId.Create(("wcs-QutritExtremeSixLevels-"+name.Replace(".","-").Replace("_","-")).ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QutritExtremeSixLevels."+name.Split('.')[name.Split('.').Length - 1]),H(title),StatementSource.FromAuthor(Disp(f)),
        p ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role,resolution);
    private static AssessedProvenance Wcs => AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/wangchensong2026extremeappt"));

    private static Formula ClaimBody => And(All("rho",M,Imp(In(Id("rho"),Call("Set.extremePoints",R,Id("apStates"))),Le(Card(Call("spectrum",C,Id("rho"))),Int(6)))),Ex("rho",M,And(In(Id("rho"),Call("Set.extremePoints",R,Id("apStates"))),Eq(Card(Call("spectrum",C,Id("rho"))),Int(6)))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The achievable upper bound on the number of distinct eigenvalues of extreme two-qutrit absolutely PPT states is six.",H("Extreme two-qutrit states have at most six spectral levels"),Blocks(
        Desc("apStates","Absolutely PPT density matrices",Eq(Id("apStates"),Typed(States,Call("Set",M))),
            "Definition 1, page 3: “A separable (resp. PPT) state ρ is called absolutely separable (resp. PPT) if it remains separable (PPT) regardless of what global unitary operation is applied. That is, for any unitary matrix U, the state UρU† is separable (resp. PPT).” Here the PPT case is represented by the positive semidefinite trace-one Matrix condition and APPT.",DescribeRole.Definition,Wcs),
        Desc("claim","The achievable upper bound",Eq(Id("claim"),Parenthesized(ClaimBody)),
            "Section VII, Conclusions, page 29: “Fourth, what is the achievable upper bound of distinct eigenvalues of extreme two-qutrit AP states?” The encoding uses Set.extremePoints over the real scalar field and the complex spectrum. Set.ncard counts distinct eigenvalues without multiplicity. The upper bound is six, and six is attained.",DescribeRole.Definition,Wcs),
        Desc("result","Six is the sharp bound",ClaimBody,
            "Every extreme two-qutrit AP state has at most six distinct eigenvalues, and an extreme state with six distinct eigenvalues exists. A feasible two-sided perturbation excludes seven or more levels; the supporting functional proves attainment.",p:AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/wangchensong2026extremeappt")),resolution:new OpenProblemResolutionClaim(ProblemSlugRef.Create("wang-chen-song-2026-appt-extreme-six-levels"),ResolutionKind.Proved)))));
}
