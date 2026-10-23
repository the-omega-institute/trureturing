using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritHildebrandSufficiencyDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(Num(-n)) : Num(n);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((p,i) => i == 0 ? new[] {Id(p)} : new[] {Dot,Id(p)}).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Q(s), [..xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists,Sp,Parenthesized(Seq(Id(s),Colon,t)),Comma,Sp,b);
    private static Formula Bind(Formula b, params (string,Formula)[] xs) { for (var i=xs.Length-1;i>=0;i--) b=xs[i].Item1.Length==0 ? Seq(OpenBracket,xs[i].Item2,CloseBracket,Sp,b) : All(xs[i].Item1,xs[i].Item2,b); return b; }
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i)=> i==0 ? new[] {Parenthesized(f)} : new[] {Land,Sp,Parenthesized(f)}).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a),Rightarrow,Sp,Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a,F.Eq,b);
    private static Formula Le(Formula a, Formula b) => Seq(a,Leq,Sp,b);
    private static Formula Arr(Formula a, Formula b) => Seq(a,To,Sp,b);
    private static Formula Prod(Formula a, Formula b) => Parenthesized(Seq(a,Times,Sp,b));
    private static Formula Add(Formula a, Formula b) => Seq(a,Plus,b);
    private static Formula Mul(Formula a, Formula b) => Seq(a,Cdot,Sp,b);
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula Mat(Formula i, Formula f) => Call("Matrix",i,i,f);
    private static Formula Ps(Formula a) => Seq(Parenthesized(a),Dot,Id("PosSemidef"));
    private static Formula Tr(Formula a) => Seq(Parenthesized(a),Dot,Id("trace"));
    private static Formula Re(Formula a) => Seq(Parenthesized(a),Dot,Id("re"));
    private static Formula Conj(Formula a) => Call("Matrix.conjTranspose",a);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a,Colon,t));
    private static Formula Lambda(string s, Formula t, Formula b) => Parenthesized(Seq(Id("fun"),Sp,Typed(Id(s),t),Sp,Mapsto,Sp,b));
    private static Formula Sum(string s, Formula t, Formula b) => Seq(new Formula.Subscript(F.Sum,Seq(Id(s),Colon,t)),Sp,b);
    private static Formula Pow(Formula a,int n) => new Formula.Power(Parenthesized(a),Int(n));
    private static Formula Range(Formula l) => Call("Set.range",l);
    private static Formula J => Prod(Fin(Int(3)),Fin(Int(3)));
    private static Formula M => Mat(J,C);
    private static Formula L => Arr(Fin(Int(9)),R);
    private static Formula Ordered(Formula H,Formula n,Formula? cast) => Lambda("i",Fin(n),App(Seq(H,Dot,new Formula.Subscript(Id("eigenvalues"),Int(0))),cast is null ? Call("Fin.cast",Id("i")) : Call("Fin.cast",cast,Id("i"))));
    private static Formula Diag(Formula i, Formula l) => Call("Matrix.diagonal",Lambda("i",i,Typed(App(l,Id("i")),C)));
    private static Formula Conjugate(Formula i,Formula U,Formula l) => Mul(Mul(Typed(U,Mat(i,C)),Diag(i,l)),Conj(Typed(U,Mat(i,C))));
    private static Formula StandardBinders(Formula body) => Bind(body,("I",Id("Type")),("",Call("Fintype",Id("I"))),("",Call("DecidableEq",Id("I"))));
    private static DocumentBlock Desc(string name,string title,Formula f,string prose,DescribeRole role=DescribeRole.Theorem,AssessedProvenance? p=null) => Describe.Lean(
        DescribeId.Create(("wcs-QutritHildebrandSufficiency-"+name.Replace(".","-").Replace("_","-")).ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QutritHildebrandSufficiency."+name.Split('.')[name.Split('.').Length - 1]),H(title),StatementSource.FromAuthor(Disp(f)),
        p ?? AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);
    private static AssessedProvenance Hildebrand => AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra"));

    private static Formula Spectral(bool range)
    {
        var k=Id("k");var rho=Id("rho");var d=Mul(Int(3),Parenthesized(Add(Int(3),k)));var j=Prod(Fin(Int(3)),Fin(Add(Int(3),k)));
        var eig=Ordered(range ? Id("H") : Q("hrho.isHermitian"),d,null);
        Formula body;
        if(range) body=Eq(Call("spectrum",C,rho),Call("Set.image",Q("Complex.ofReal"),Range(eig)));
        else body=Ex("l",Arr(Fin(d),R),And(Call("Antitone",Id("l")),All("i",Fin(d),Le(Int(0),Call("l",Id("i")))),Eq(Sum("i",Fin(d),Call("l",Id("i"))),Int(1)),Ps(Call("K1",Call("boundaryValues",k,Id("l")))),Ps(Call("K2",Call("boundaryValues",k,Id("l")))),Eq(Re(Tr(Mul(rho,rho))),Sum("i",Fin(d),Pow(Call("l",Id("i")),2))),Eq(Id("l"),eig)));
        body=range ? All("H",Call("Matrix.IsHermitian",rho),body) : All("hrho",Ps(rho),Imp(And(Eq(Tr(rho),Int(1)),Call("APPT",rho)),body));
        return Bind(body,("k",N),("rho",Mat(j,C)));
    }
    private static Formula Trace(bool inequality)
    {
        var i=Id("I");var w=Id("w");var l=Id("l");var u=Id("U");
        var tr=Re(Tr(Mul(Diag(i,w),Conjugate(i,u,l))));
        Formula body=inequality ? Imp(Call("Monovary",Lambda("i",i,new Formula.Negate(Call("w",Id("i")))),l),Le(Sum("i",i,Mul(Call("w",Id("i")),Call("l",Id("i")))),tr)) : Eq(tr,Sum("i",i,Sum("j",i,Mul(Mul(Call("w",Id("i")),Call("RHLinalg.normSqMatrix",Typed(u,Mat(i,C)),Id("i"),Id("j"))),Call("l",Id("j"))))));
        return StandardBinders(Bind(body,("w",Arr(i,R)),("l",Arr(i,R)),("U",Call("unitaryGroup",i,C))));
    }
    private static Formula Sorted(bool anti,bool unique)
    {
        var carrier=anti || unique ? "J" : "I";
        var i=Id(carrier);var n=Id("n");var a=Id("A");var h=Id("H");var e=Id("e");var u=Id("U");var l=Id("l");
        Formula WithEntries(Formula entry) => Mul(Mul(Typed(u,Mat(i,C)),Call("Matrix.diagonal",Lambda("i",i,Typed(entry,C)))),Conj(Typed(u,Mat(i,C))));
        var eig=Ordered(h,n,Q("hc.symm"));var eq=Eq(a,WithEntries(App(l,App(e,Id("i")))));
        Formula body=anti ? Call("Antitone",eig) : unique ? Imp(And(Call("Antitone",l),eq),Eq(eig,l)) : Ex("U",Call("unitaryGroup",i,C),Eq(a,WithEntries(App(eig,App(e,Id("i"))))));
        if(unique) body=Bind(body,("l",Arr(Fin(n),R)),("e",Call("Equiv",i,Fin(n))),("U",Call("unitaryGroup",i,C)));
        else if(!anti) body=All("e",Call("Equiv",i,Fin(n)),body);
        return Bind(body,(carrier,Id("Type")),("",Call("Fintype",i)),("",Call("DecidableEq",i)),("n",N),("hc",Eq(Call("Fintype.card",i),n)),("A",Mat(i,C)),("H",Call("Matrix.IsHermitian",a)));
    }
    private static Formula Criterion(bool iff)
    {
        var rho=Id("rho");var eig=Ordered(iff ? Q("hp.isHermitian") : Id("H"),Int(9),null);
        var cond=And(Ps(Call("K1",eig)),Ps(Call("K2",eig)));
        var body=iff ? Imp(Eq(Tr(rho),Int(1)),Seq(Call("APPT",rho),Iff,Sp,cond)) : Imp(cond,Call("APPT",rho));
        return Bind(body,("rho",M),(iff ? "hp" : "H",iff ? Ps(rho) : Call("Matrix.IsHermitian",rho)));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two Hildebrand pencils characterize absolutely PPT density matrices on two qutrits.",H("Hildebrand sufficiency on two qutrits"),Blocks(
        Desc("SpectralBridge.spectral_reduction_ordered","Ordered spectral necessity",Spectral(false),"The eigenvalues are the sorted eigenvalues chosen in the spectral reduction. The proof argument of Fin.cast is omitted; it is the cardinality equality for Fin 3 × Fin (3+k).",p:Hildebrand),
        Desc("SpectralBridge.spectrum_eq_ordered_range","Spectrum as an ordered range",Spectral(true),"The complex spectrum is the real embedding of the range of the sorted eigenvalues. The proof argument of Fin.cast is omitted; it is the cardinality equality for Fin 3 × Fin (3+k)."),
        Desc("TraceBridge.trace_diagonal_conjugate","Trace and squared unitary entries",Trace(false),"Expansion of the trace gives the finite sum with squared moduli of the unitary entries."),
        Desc("TraceBridge.trace_lower_of_monovary_diagonalization","Trace lower bound",Trace(true),"Oppositely ordered weights give a lower bound for the trace of the conjugated diagonal operator."),
        Desc("OrderedDiagonalization.sorted_diagonalization","Sorted diagonalization",Sorted(false,false),"A unitary conjugates the diagonal matrix indexed by the chosen equivalence to the Hermitian matrix."),
        Desc("Sufficiency.sorted_eigenvalues_antitone","Descending eigenvalues",Sorted(true,false),"Reindexing by the cardinality equality preserves descending order."),
        Desc("Sufficiency.hildebrand_sufficiency","Hildebrand sufficiency",Criterion(false),"Positivity of both real pencils implies positivity of every partial transpose after unitary conjugation. Hildebrand, Corollary 4, pages 5–6. Fin.cast omits the proof of the carrier cardinality equality.",p:Hildebrand),
        Desc("Criterion.boundary_values_zero","Two-qutrit boundary coordinates",All("l",L,Eq(Call("boundaryValues",Int(0),Id("l")),Id("l"))),"When both local dimensions are three, all nine boundary coordinates are unchanged."),
        Desc("Criterion.hildebrand_criterion","Hildebrand equivalence",Criterion(true),"For a positive trace-one matrix, absolute PPT is equivalent to positivity of both Hildebrand pencils. Hildebrand, Corollary 4, pages 5–6. Fin.cast omits the proof of the carrier cardinality equality.",p:Hildebrand),
        Desc("Criterion.sorted_eigenvalues_of_diagonalization","Identification of sorted diagonal entries",Sorted(false,true),"An antitone diagonal list in a unitary diagonalization equals the sorted eigenvalues."))));
}
