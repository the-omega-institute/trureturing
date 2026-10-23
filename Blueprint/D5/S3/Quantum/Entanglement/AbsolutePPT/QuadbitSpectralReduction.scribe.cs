using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitSpectralReductionDocument : IScribeDocumentDefinition
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
    private static Formula Lt(Formula x, Formula y) => Seq(x, F.Lt, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Prod(Formula x, Formula y) => Parenthesized(Seq(x, Times, Sp, y));
    private static Formula Matrix(Formula i, Formula j, Formula field) => Call("Matrix", i, j, field);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static Formula Trace(Formula m) => Call("Matrix.trace", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);



    private static Formula J => Prod(Fin(Int(4)),Fin(Int(4)));
    private static Formula l => Id("l");
    private static Formula rho => Id("rho");
    private static Formula BoundaryStatement()
    {
        var q=Id("q"); var value=Call("val",q);
        var index=Seq(Id("if"),Sp,Lt(value,Int(3)),Sp,Id("then"),Sp,value,
            Sp,Id("else"),Sp,Add(Int(7),value));
        return All("l",Arrow(Fin(Int(16)),R),All("q",Fin(Int(9)),
            Eq(Call("boundaryValues16",l,q),Call("l",Parenthesized(Seq(index,Colon,Fin(Int(16))))))));
    }
    private static Formula SpectralStatement()
    {
        var boundary=Call("boundaryValues16",l);
        var purity=Eq(Call("Complex.re",Trace(Mul(rho,rho))),
            Sum("i",Fin(Int(16)),Pow(Call("l",Id("i")),2)));
        var conclusion=And(Call("Antitone",l),All("i",Fin(Int(16)),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(Int(16)),Call("l",Id("i"))),Int(1)),
            PSInt(Call("K1",boundary)),PSInt(Call("K2",boundary)),purity);
        var exists=Seq(Exists,Sp,Parenthesized(Seq(l,Colon,Arrow(Fin(Int(16)),R))),Comma,Sp,conclusion);
        return All("rho",Matrix(J,J,C),Imp(And(PSInt(rho),Eq(Trace(rho),Int(1)),Call("APPT",rho)),exists));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal four-by-four APPT density matrices satisfy the two qutrit corner constraints on their largest three and smallest six spectral values.",
        H("Four-by-four APPT spectral reduction"),Blocks(
            Desc("QuadbitSpectralReduction","boundaryValues16","The nine boundary values in dimension sixteen",BoundaryStatement(),
                "Indices are zero-based. The boundary selector retains spectrum entries 0, 1, 2, 10, 11, 12, 13, 14, 15, and omits the seven middle values. The packing equivalence uses all sixteen coordinates; it does not change the physical local tensor factors."),
            Desc("QuadbitSpectralReduction","spectral_reduction","Four-by-four density-to-spectrum reduction",SpectralStatement(),
                "Every positive semidefinite trace-one matrix on Fin 4 × Fin 4 that remains positive under partial transpose after every global unitary conjugation has an antitone nonnegative sixteen-coordinate spectrum of mass one. Its selected largest three and smallest six values satisfy both real qutrit boundary LMIs, and its real trace-square equals the sum of spectral squares. The proof reuses the existing ordered spectral diagonalization and the existing Bell calculation. It embeds that calculation into the genuine local Fin 3 × Fin 3 corner, extends each unitary by the identity on the seven complementary product positions, and compresses partial transpose only along product coordinates. An arbitrary global coordinate equivalence is used as a unitary packing, never as an asserted symmetry of partial transpose. These two constraints are necessary; this theorem does not assert that they characterize four-by-four APPT states. No statement about physical preparation or experimental observability is included. The bridge is consumed by the exact dimension-sixteen purity bound.",DescribeRole.Theorem))));
}
