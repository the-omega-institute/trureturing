using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRatioLogConcavity;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpvishnyakovazhang2025unimodality");
    private const string Prefix = "D5/S3/Analytic/BesselRatioLogConcavity/Result.";
    private const string Quotation = "Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive rational series disproves log-concavity of a modified Bessel ratio.",
        H("A modified Bessel ratio need not be log-concave"), Blocks(
            Describe.Lean(DescribeId.Create("modified-bessel-series"),
                DeclarationHandle.Create(Prefix + "besselI"),
                H("The modified Bessel function of the first kind"),
                StatementSource.FromAuthor(Disp(BesselFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Printed page 11 of arXiv:2408.01755v2 states: “with a > 0, b ≥ 0, ν > −1, µ > 0 and Iν standing for the modified Bessel function of the first kind.” It then states verbatim: “Using the standard power series expansion of Iν [28, p.217] we have”. The following displayed expansion of the ratio uses the series Iν(z)=∑ₖ₌₀∞(z/2)^(2k+ν)/(k! Γ(k+ν+1)). The definition is this real infinite sum, with the natural number 2k coerced to a real exponent. For z>0 and ν>−1 the series is summable: after the Gamma–Pochhammer identity its successive ratio tends to zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bessel-log-concavity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The positive-order log-concavity clause"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 1, printed page 12, with line breaks joined: “" + Quotation + "”")),
                    Paragraph(Text("The claim quantifies over all real orders nu1≥nu2>0 and all scales 0<a1≤a2. It states concavity on the entire positive real half-line of the logarithm of the standard modified Bessel ratio. Positivity of the series on this domain makes that the usual log-concavity assertion. The parameter b in the source does not occur in the ratio. Its unimodality clause is a separate assertion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bessel-log-concavity-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An exact infinite-series counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take equal orders nu1=nu2=1/10 and scales a1=1,a2=2. Write S(w)=∑ₖ₌₀∞ w^k/(k! (11/10)ₖ). The Gamma–Pochhammer identity gamma_pochhammer gives Iν(t)/Iν(2t)=2^(−ν) S(t²/4)/S(t²). Gamma factors cancel, and the positive real power factor is common to all three points.")),
                    Paragraph(Text("For a nonnegative rational w, let L(w) be the sum over 0≤k<60, let t60(w) be the term of index 60, and put rho(w)=w/(61·(611/10)). Every successive ratio starting at index 60 is at most rho(w). When rho(w)<1, the infinite series lies between L(w) and L(w)+t60(w)/(1−rho(w)). Exact rational arithmetic gives S(9/16)≥1.584, S(225/16)≥223.368 and S(81/4)≥894.574, while S(81/16)≤15.316, S(9/4)≤4.447 and S(225/4)≤264068.")),
                    Paragraph(Text("These bounds imply S(9/16)S(225/16)S(81/4)²>S(81/16)²S(9/4)S(225/4). Thus R(3/2)R(15/2)>R(9/2)² for R(t)=I₁⁄₁₀(t)/I₁⁄₁₀(2t). Taking logarithms contradicts concavity at the midpoint 9/2. This disproves the universal log-concavity clause; it leaves unimodality and the full parameter range of log-concavity unresolved."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity"),
                    ResolutionKind.Refuted)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]);
    }
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Pos(Formula value) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula BesselFormula()
    {
        var k = V("k");
        var exponent = Add(Mul(D(2), k), V("nu"));
        var summand = new Formula.Fraction(
            new Formula.Power(Parenthesized(new Formula.Fraction(V("z"), D(2))), exponent),
            Mul(Call("Nat.factorial", k), Call("Real.Gamma", Add(Add(k, V("nu")), D(1)))));
        var sum = Seq(new Formula.Subscript(Seq(Sum, Sp, Apos), Seq(k, Colon, Sp, N)), Sp, summand);
        return All("nu", R, All("z", R, Eqn(Call("besselI", V("nu"), V("z")), sum)));
    }
    private static Formula ClaimBody()
    {
        var x = V("x");
        var ratio = new Formula.Fraction(
            Call("besselI", V("nu1"), Mul(V("a1"), x)),
            Call("besselI", V("nu2"), Mul(V("a2"), x)));
        var function = Seq(x, Colon, Sp, R, Mapsto, Sp, Call("Real.log", ratio));
        var concave = Call("ConcaveOn", R, Call("Set.Ioi", D(0)), function);
        return All("nu1", R, All("nu2", R, All("a1", R, All("a2", R,
            Imp(Pos(V("nu2")), Imp(Leq(V("nu2"), V("nu1")),
                Imp(Pos(V("a1")), Imp(Leq(V("a1"), V("a2")), concave))))))));
    }
}
