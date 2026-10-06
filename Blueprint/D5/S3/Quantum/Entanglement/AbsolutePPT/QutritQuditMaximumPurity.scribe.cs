using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritQuditMaximumPurityDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static Formula OfReal(Formula r) => Call("Complex.ofReal", r);
    private static Formula CastN(Formula n) => Parenthesized(Seq(n, Colon, R));
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);


    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/QuantumStates/ahiablekothakondawinter2026geometry");
    private static readonly LibraryNoteRef Tran=LibraryNoteRef.Create("D5/L/QuantumStates/tran2026spectralappt");
    private static Formula n => Id("n");
    private static Formula p => Id("p");
    private static Formula rho => Id("rho");
    private static Formula J => Prod(Fin(Int(3)),Fin(n));
    private static Formula StateType => Matrix(J,J,C);
    private static Formula Purity => Call("Complex.re",Trace(Mul(rho,rho)));
    private static Formula Maximum => Call("max",Frac(Add(Mul(Int(3),CastN(n)),Int(8)),Pow(Add(Mul(Int(3),CastN(n)),Int(2)),2)),Frac(Int(3),Mul(Int(8),CastN(n))));
    private static Formula PrescribedState()
    {
        var ij=Id("ij");
        var first=Call("Prod.fst",ij);
        var second=Call("Fin.val",Call("Prod.snd",ij));
        var origin=And(Eq(first,Int(0)),Eq(second,Int(0)));
        Formula If(Formula condition, Formula yes, Formula no) =>
            Seq(Id("if"),Sp,Parenthesized(condition),Sp,Id("then"),Sp,yes,Sp,Id("else"),Sp,no);
        var small=Frac(Parenthesized(If(origin,Int(3),Int(1))),Add(Mul(Int(3),CastN(n)),Int(2)));
        var large=Frac(Parenthesized(If(Eq(first,Int(0)),Int(2),Int(1))),Mul(Int(4),CastN(n)));
        var entries=OfReal(Parenthesized(Seq(If(Le(n,Int(8)),small,large),Colon,R)));
        var lambda=Seq(Id("fun"),Sp,Parenthesized(Seq(ij,Colon,J)),Sp,Mapsto,Sp,entries);
        return Call("Matrix.diagonal",Parenthesized(lambda));
    }
    private static Formula ExistsState(Formula value, bool prescribed = false)
    {
        var density=And(PSInt(rho),Eq(Trace(rho),Int(1)));
        var state=And(density,Call("APPT",rho),Eq(Purity,value));
        var body=prescribed ? And(Eq(rho,PrescribedState()),state) : state;
        return Seq(Exists,Sp,Parenthesized(Seq(rho,Colon,StateType)),Comma,Sp,body);
    }
    private static Formula ClaimDefinition()
    {
        var set=Seq(OpenBrace,p,Colon,R,Sp,Bar,Sp,ExistsState(p),CloseBrace);
        var body=And(Eq(Call("sSup",set),Maximum),ExistsState(Maximum,true));
        return Seq(Id("claim"),Iff,Sp,All("n",N,Imp(Le(Int(3),n),body)));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least three, the literal qutrit APPT purity supremum equals the larger candidate purity and is attained by the prescribed diagonal state.",
        H("Exact qutrit–qudit APPT maximum purity"),Blocks(
            Desc("QutritQuditMaximumPurity","claim","Exact maximum and attainment",ClaimDefinition(),
                "Ahiable–Kothakonda–Winter, Conjecture 6.7, page 29: Let 𝒫_{m,n} ⊆ APPT_{m,n} be the inscribed absolute PPT polytope with 2 ≤ m ≤ n, n > 2. Then max_{λ∈APPT_{m,n}} ∑_{i=1}^{mn} λ_i² = max_{λ∈𝒫_{m,n}} ∑_{i=1}^{mn} λ_i² and occurs at the spectra given by Eq. (44). The encoding substitutes m=3 and Corollary 6.4's two candidate values, quantifies every natural n≥3, uses density matrices on Fin 3 × Fin n, and expresses a maximum by the real sSup together with attainment at an explicit computational-basis diagonal state. For 3≤n≤8 the entry at (0,0) is 3/(3n+2) and all other entries are 1/(3n+2), giving the spectrum (3,1,…,1)/(3n+2). For n≥9 the entries with first-factor index 0 are 2/(4n) and the other entries are 1/(4n), giving n copies of 2/(4n) and 2n copies of 1/(4n). The second index test uses Fin.val, and the real diagonal entries are cast to complex numbers by Complex.ofReal. APPT is the literal predicate defined in QutritPerturbationAttainment; the purity is Complex.re of Matrix.trace (rho*rho). All displayed quotients are real division. Tran, remark after Theorem A, page 4: Determining the exact maximum APPT purity remains open.",provenance:AssessedProvenance.FromRepo(Source,Tran)),
            Desc("QutritQuditMaximumPurity","result","Unconditional exact maximum",Id("claim"),
                "The unconditional proof combines exact finite-sector dual certificates with a K1-only uniform cone estimate and the prescribed explicit diagonal density matrices. It proves this qutrit sector of the source conjecture and leaves m≥4 and APPT versus absolute separability open.",DescribeRole.Theorem,AssessedProvenance.FromRepo(Source,Tran)))));
}
