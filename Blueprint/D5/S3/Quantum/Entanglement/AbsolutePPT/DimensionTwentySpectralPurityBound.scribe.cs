using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class DimensionTwentySpectralPurityBoundDocument : IScribeDocumentDefinition
{
    private static Formula D(long n) => Num(n);
    private static Formula X(string n) => F.Id(n);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(X(name), [.. xs]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp,y);
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Sp,Par(q));
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i) => i == 0 ? new[] {Par(f)} : new[] {Land, Sp,Par(f)}).ToArray());
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp,y);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Sq(Formula x) => new Formula.Power(Par(x), D(2));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Sum(string n, Formula t, Formula f) => Seq(new Formula.Subscript(F.Sum, Seq(X(n), Colon, t)), Par(f));
    private static Formula Vector(Formula n) => Arrow(Fin(n), R);
    private static Formula Mass(Formula n, Formula l) => Sum("i", Fin(n), new Formula.Apply(l, [X("i")]));
    private static Formula Purity(Formula n, Formula l) => Sum("i", Fin(n), Sq(new Formula.Apply(l, [X("i")])));
    private static Formula Feasible(Formula n, Formula l) => And(Call("Antitone", l),
        All("i", Fin(Add(n,D(9))), Le(D(0), new Formula.Apply(l, [X("i")]))),
        Eqn(Mass(Add(n,D(9)),l),D(1)),
        Call("PosSemidef",Call("K1",Call("boundaryValues",n,l))),
        Call("PosSemidef",Call("K2",Call("boundaryValues",n,l))));
    private static DocumentBlock Desc(string name, string title, Formula f, string prose) =>
        Describe.Lean(DescribeId.Create("appt-dimension-twenty-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create()
    {
        var l=X("l"); var bound=Frac(D(7),D(121));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every feasible rank-three length-twenty spectrum has purity at most 7/121.",
            H("Length-twenty spectral purity bound"), Blocks(
            Desc("spectral_purity_bound", "Universal spectral inequality",
                All("l",Vector(D(20)),Imp(Feasible(D(11),l),Le(Purity(D(20),l),bound))),
                "For every antitone nonnegative real spectrum on Fin 20 with mass one and both rank-three boundary matrices positive semidefinite, the square sum is at most 7/121. The baseline-frozen N6 and N7 rational certificate bounds give the endpoints at lengths 18 and 21. N7 exposes its original private certificate without changing its coefficients or proof. The same-delivery new SpectralBoundaryTransfer.spectral_bound_transfer first gives length 19 using a=2, then length 20 using a=1. Expanding this live inference stops at the baseline endpoints, not at the new transfer. Its arbitrary ordered-tuple construction, actual deletion, repeated insertion and normalization provide the structural content of this upper bound. Length 19 is a spectral intermediate. This inequality does not assert literal four-by-five APPT or settle the unrestricted APPT purity conjecture."))));
    }
}
