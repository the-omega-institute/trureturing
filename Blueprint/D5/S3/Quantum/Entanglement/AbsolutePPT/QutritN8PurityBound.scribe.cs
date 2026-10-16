using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QutritN8PurityBoundDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula C => Seq(Mathbb, Grp(Id("C")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula DensityStatement()
    {
        var rho=Id("rho");
        var j=Prod(Fin(Int(3)),Fin(Int(8)));
        var hypotheses=And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho));
        return All("rho",Matrix(j,j,C),Imp(hypotheses,
            Le(Call("Complex.re",Trace(Mul(rho,rho))),Frac(Int(32),Pow(Int(26),2)))));
    }
    private static Formula CertificateStatement()
    {
        var l=Id("l"); var i=Id("i");
        var b=Call("boundaryValues",Int(5),l);
        var sum=Seq(new Formula.Subscript(F.Sum,Seq(i,Colon,Fin(Int(24)))),Sp,Pow(Call("l",i),2));
        var mass=Seq(new Formula.Subscript(F.Sum,Seq(i,Colon,Fin(Int(24)))),Sp,Call("l",i));
        return All("l",Seq(Fin(Int(24)),To,Sp,R),
            Imp(And(Call("Antitone",l),Le(Int(0),Call("l",Int(23))),Eq(mass,Int(1)),
                PSInt(Call("K1",b)),PSInt(Call("K2",b))),Le(sum,Frac(Int(32),Pow(Int(26),2)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal qutrit APPT density matrices satisfy the sharp purity bound for n = 8.",
        H("Qutrit APPT purity for n = 8"),Blocks(
            Desc("QutritN8PurityBound","certificate_bound","Sharp ordered-spectrum certificate",CertificateStatement(),
                "For any antitone real twenty-four-vector of mass one with nonnegative last entry, the two qutrit boundary matrices imply squared mass at most 32/26². The boundary selector is QutritSpectralReduction.boundaryValues 5; K1 and K2 are its real three-dimensional matrices. This certificate has no tensor-factor hypothesis and applies to both the 3-by-8 and 4-by-6 density reductions. Its proof is an exact rational gap certificate.",DescribeRole.Theorem),
            Desc("QutritN8PurityBound","purity_bound","Sharp density-matrix purity estimate",DensityStatement(),
                "Every positive semidefinite trace-one complex matrix on Fin 3 × Fin 8 satisfying literal APPT has the stated real trace-square bound. APPT means that the partial transpose of U rho Uᴴ is positive semidefinite for every unitary U, as defined in QutritPerturbationAttainment. The proof applies QutritSpectralReduction.spectral_reduction to obtain ordered spectral certificate coordinates with both boundary LMIs and matching purity, then consumes the rational gap certificate. All displayed quotients are real division.",DescribeRole.Theorem))));
}
