using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class QuadbitSpectralPurityBoundDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
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
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Value(int i) => Call("l",Int(i));
    private static Formula KDefinition(string name, int diagonalMiddle, int upperRight)
    {
        Formula[] entries=[Mul(Int(2),Value(15)),Sub(Value(14),Value(0)),Sub(Value(upperRight),Value(1)),
            Sub(Value(14),Value(0)),Mul(Int(2),Value(diagonalMiddle)),Sub(Value(11),Value(2)),
            Sub(Value(upperRight),Value(1)),Sub(Value(11),Value(2)),Mul(Int(2),Value(10))];
        var matrix=Seq(Bang,Bang,OpenBracket,entries[0],Comma,entries[1],Comma,entries[2],Semi,
            entries[3],Comma,entries[4],Comma,entries[5],Semi,
            entries[6],Comma,entries[7],Comma,entries[8],CloseBracket);
        return All("l",Arrow(Fin(Int(16)),R),Eq(Call(name,Id("l")),matrix));
    }
    private static Formula SpectralStatement()
    {
        var l=Id("l");
        var hypotheses=And(Call("Antitone",l),All("i",Fin(Int(16)),Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",Fin(Int(16)),Call("l",Id("i"))),Int(1)),
            PSInt(Call("K1",l)),PSInt(Call("K2",l)));
        return All("l",Arrow(Fin(Int(16)),R),Imp(hypotheses,
            Le(Sum("i",Fin(Int(16)),Pow(Call("l",Id("i")),2)),Frac(Int(2),Int(27)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two qutrit boundary constraints imply the sharp dimension-sixteen spectral purity estimate.",
        H("Dimension-sixteen spectral purity by interpolation"),Blocks(
            Desc("QuadbitSpectralPurityBound","K1","The first dimension-sixteen boundary matrix",KDefinition("K1",13,12),
                "For a descending sixteen-coordinate spectrum, retain the largest three and smallest six values in the first qutrit boundary matrix. Indices are zero-based. These constraints are necessary for literal four-by-four APPT via QuadbitSpectralReduction; sufficiency is not claimed."),
            Desc("QuadbitSpectralPurityBound","K2","The second dimension-sixteen boundary matrix",KDefinition("K2",12,13),
                "The second real symmetric boundary matrix exchanges spectral indices 12 and 13 relative to the first. Both matrices enter the interpolation certificate."),
            Desc("QuadbitSpectralPurityBound","spectral_purity_bound","The sharp sixteen-coordinate spectral estimate",SpectralStatement(),
                "For every antitone nonnegative real sixteen-coordinate vector of mass one with K1 and K2 positive semidefinite, its square sum is at most 2/27. Let t be coordinate 9. Testing K1 on the all-ones vector bounds the largest-three sum by the smallest-six sum and gives t at most 1/13. If t is at most 1/18, insert two copies of t into the middle, divide by mass 1+2t, and apply QutritN6PurityBound.certificate_bound. Otherwise delete coordinate 9, divide by mass 1-t, and apply QutritN5PurityBound.certificate_bound. Both transformations preserve the boundary matrices up to a positive scalar. Their square sums are respectively P+2t² and P-t²; two exact quadratic inequalities yield 2/27, meeting at t=1/18. No APPT sufficiency statement, physical preparation, or experiment is assumed. QuadbitMaximumPurity consumes the result after the genuine local-corner spectral reduction.",DescribeRole.Theorem))));
}
