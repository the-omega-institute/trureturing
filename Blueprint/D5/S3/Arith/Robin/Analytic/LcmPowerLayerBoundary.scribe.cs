using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class LcmPowerLayerBoundaryDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/fankobayashimolnar2025family");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The LCM power layer comparison above an explicit threshold independent of the layer index.",
        H("Uniform LCM power layer boundaries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("layer-boundary-explicit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_explicit"),
                H("An explicit threshold for all layers"),
                StatementSource.FromAuthor(ExplicitClaim()), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every real kappa>1, put u=max(6,(2^(kappa+1.01))^(1/(kappa-1))). "
                        + "For every real x>=exp(u) and every natural ell>=2, "
                        + "F(kappa,x,1)<F(kappa,x^(1/ell),ell). "
                        + "The function F is the real-valued expression in Definition 4.2 "
                        + "of Fan, Kobayashi and Molnar, A family of analogues to the Robin criterion. "
                        + "The threshold depends on kappa alone and is not claimed to be optimal.")),
                    Paragraph(Text(
                        "Put B(s)=log((1+s)^kappa-s^kappa) and phi(s)=s*B'(s). "
                        + "The logarithmic power difference is concave, its derivative "
                        + "decreases on the positive half-line, and phi strictly increases there. "
                        + "For u=log(x), let v=2/u and r=2/(u+2). The elasticity formula gives "
                        + "phi(v)>=kappa*(r-r^kappa). The threshold implies u>=6 and "
                        + "u^(kappa-1)>=2^(kappa+1.01)>2*2^kappa. Hence u*r>=3/2 "
                        + "and u*r^kappa<=2^kappa/u^(kappa-1)<1/2, so u*phi(2/u)>kappa. "
                        + "If n>=2 and 0<s<=n/u, decrease of B' and increase of phi give "
                        + "n*B'(s)>=u*phi(n/u)>=u*phi(2/u)>kappa.")),
                    Paragraph(Text(
                        "Set y=x^(1/ell), h=y^(-ell), and s=(1-h)/(y-1). "
                        + "The logarithm bound log(y)<=y-1 gives s<=ell/u. Factoring F gives "
                        + "kappa*log(y)*F(kappa,y,ell)=B(s)-B(s-h) and "
                        + "kappa*ell*log(y)*F(kappa,y^ell,1)=B(h). "
                        + "Concavity gives B(s)-B(s-h)>=h*B'(s), whereas B(h)<kappa*h. "
                        + "The explicit derivative bound yields ell*(B(s)-B(s-h))>B(h), "
                        + "which is the required strict comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("layer-boundary-uniform"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform"),
                H("A threshold independent of the layer"),
                StatementSource.FromAuthor(UniformClaim()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every real kappa>1 there is a real threshold X such that "
                    + "for every real x>=X, every natural ell>=2 and every real xell>1, "
                    + "F(kappa,xell,ell)=F(kappa,x,1) implies x^(1/ell)<xell. "
                    + "This follows from the explicit layer-base comparison by "
                    + "choosing X=exp(max(6,(2^(kappa+1.01))^(1/(kappa-1)))). "
                    + "This is the single settlement result, in the literal layer-base form of Remark 5.5."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fan-kobayashi-molnar-2026-remark-5-5"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("layer-function-strict-decrease"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.F_strictAntiOn"),
                H("Strict decrease in the base"),
                StatementSource.FromAuthor(MonotonicityClaim()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every kappa>1 and every natural ell>=1, F(kappa,.,ell) strictly "
                    + "decreases on (1,infinity). This statement is the natural-layer restriction of source Theorem 4.3. The repository gives an independent proof that does not use that theorem. "
                    + "For t>0 write S(n,t)=t+...+t^n and D(n,t)=dS(n,t)/dt. "
                    + "Termwise comparison gives t*D(n,t)<=n*S(n,t), which implies "
                    + "D(n,t)/S(n,t)<=D(n+1,t)/S(n+1,t) for n>=1. Together with "
                    + "strict increase of phi and positivity of B', this makes "
                    + "B(S(n+1,t))-B(S(n,t)) strictly increasing and positive. "
                    + "The case n=0 follows directly from B'>0 and B(0)=0. "
                    + "Substituting t=1/y makes the numerator of F strictly decrease, "
                    + "while its positive denominator kappa*log(y) increases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("layer-boundary-inverse-comparison"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_xl"),
                H("Comparison of equal-value layer bases"),
                StatementSource.FromAuthor(LayerBaseClaim()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Above the same explicit threshold, if xell>1 and "
                    + "F(kappa,xell,ell)=F(kappa,x,1), then xell>x^(1/ell). "
                    + "The explicit comparison and the strict decrease just proved give "
                    + "this conclusion without constructing an inverse function or assuming "
                    + "existence of a layer base. Thus the conclusion applies whenever "
                    + "the source layer variables satisfy their defining equality."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(Seq(Open, value, Close), exponent);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula ImpliesClaim(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies,
            Seq(Open, right, Close));
    private static Formula Threshold(Formula k) =>
        Call("exp", Call("max", D(6), Pow(Pow(D(2), Add(k,
            new Formula.Fraction(D(1, 0, 1), D(1, 0, 0)))),
            new Formula.Fraction(D(1), Subtract(k, D(1))))));
    private static Formula RootBase(Formula x, Formula ell) =>
        Pow(x, new Formula.Fraction(D(1), ell));
    private static Formula Comparison(Formula k, Formula x, Formula ell) =>
        Less(Call("lcmPowerF", k, x, D(1)), Call("lcmPowerF", k, RootBase(x, ell), ell));

    private static Formula ExplicitClaim()
    {
        var k = F.Id("kappa");
        var x = F.Id("x");
        var ell = F.Id("ell");
        return Disp(All("kappa", Real, ImpliesClaim(Less(D(1), k),
            All("x", Real, ImpliesClaim(Le(Threshold(k), x),
                All("ell", Natural, ImpliesClaim(Le(D(2), ell), Comparison(k, x, ell))))))));
    }

    private static Formula UniformClaim()
    {
        var k = F.Id("kappa");
        var threshold = F.Id("X");
        var x = F.Id("x");
        var ell = F.Id("ell");
        var layerBase = F.Id("xell");
        return Disp(All("kappa", Real, ImpliesClaim(Less(D(1), k),
            Some("X", Real, All("x", Real, ImpliesClaim(Le(threshold, x),
                All("ell", Natural, ImpliesClaim(Le(D(2), ell),
                    All("xell", Real, ImpliesClaim(Less(D(1), layerBase),
                        ImpliesClaim(Equal(Call("lcmPowerF", k, layerBase, ell),
                            Call("lcmPowerF", k, x, D(1))), Less(RootBase(x, ell), layerBase))))))))))));
    }

    private static Formula MonotonicityClaim()
    {
        var k = F.Id("kappa");
        var ell = F.Id("ell");
        var x = F.Id("x");
        var y = F.Id("y");
        return Disp(All("kappa", Real, ImpliesClaim(Less(D(1), k),
            All("ell", Natural, ImpliesClaim(Le(D(1), ell),
                All("x", Real, All("y", Real, ImpliesClaim(Less(D(1), x),
                    ImpliesClaim(Less(D(1), y), ImpliesClaim(Less(x, y),
                        Less(Call("lcmPowerF", k, y, ell), Call("lcmPowerF", k, x, ell))))))))))));
    }

    private static Formula LayerBaseClaim()
    {
        var k = F.Id("kappa");
        var x = F.Id("x");
        var layerBase = F.Id("xell");
        var ell = F.Id("ell");
        return Disp(All("kappa", Real, ImpliesClaim(Less(D(1), k),
            All("x", Real, All("xell", Real, ImpliesClaim(Le(Threshold(k), x),
                All("ell", Natural, ImpliesClaim(Le(D(2), ell),
                    ImpliesClaim(Less(D(1), layerBase),
                        ImpliesClaim(Equal(Call("lcmPowerF", k, layerBase, ell),
                            Call("lcmPowerF", k, x, D(1))), Less(RootBase(x, ell), layerBase)))))))))));
    }
}
