using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class UniformSpectralBoundDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
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
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula Statement()
    {
        var k=Id("k");var l=Id("l");
        var fd=Fin(Mul(Int(3),Parenthesized(Add(Int(3),k))));
        var h=And(Call("Antitone",l),All("i",fd,Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",fd,Call("l",Id("i"))),Int(1)),
            PSInt(Call("QutritSpectralReduction.K1",Call("QutritSpectralReduction.boundaryValues",k,l))));
        var nat=Parenthesized(Seq(Add(Int(3),k),Colon,N));
        var real=Parenthesized(Seq(nat,Colon,R));
        return All("k",N,Imp(Le(Int(8),k),All("l",Arrow(fd,R),Imp(h,
            Le(Sum("i",fd,Pow(Call("l",Id("i")),2)),Frac(Int(3),Mul(Int(8),real)))))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first qutrit spectral LMI yields the purity bound 3/(8n) for every n at least 11.",
        H("Uniform qutrit APPT spectral bound"),Blocks(
            Desc("UniformSpectralBound","uniform_spectral_bound","K1-only uniform purity estimate",Statement(),
                "Here n=3+k with k at least 8. An antitone nonnegative real spectrum of mass one is bounded using K1 alone. The argument extracts two boundary inequalities, reconstructs the spectrum from gaps, transfers a 33-ray cone certificate, and bounds every middle-coordinate mixture. The sum 3+k is formed in the natural numbers before its coercion to the reals; the quotient is real division.",DescribeRole.Theorem))));
}
