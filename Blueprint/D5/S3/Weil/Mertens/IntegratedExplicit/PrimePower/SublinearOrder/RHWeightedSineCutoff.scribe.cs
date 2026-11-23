using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHWeightedSineCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedSineCutoff";
    private static readonly LibraryNoteRef Lamzouri =
        LibraryNoteRef.Create("D5/L/Weil/lamzouri2024effective");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective linear independence gives a window bound for the actual weighted zeta sine sum.",
        H("A cutoff tradeoff for the weighted zeta sine sum"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-ordinates"),
                DeclarationHandle.Create(Owner + ".positiveOrdinates"),
                H("The distinct positive ordinates"), StatementSource.FromAuthor(OrdinatesStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here G(h,X) is a finite set of real numbers and Z is the "
                    + "set of nontrivial zeta zeros. The positive spectrum supplies the zeros through "
                    + "the inclusive cutoff X. RH puts them on the critical line, so taking imaginary "
                    + "parts is injective on that spectrum. "),
                    Ref("D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum")),
                    Paragraph(Text("Write N(X) for the canonical analytic multiplicity count in "
                    + "(0,X]. Each ordinate occurs once in G(h,X), and its zero contributes its "
                    + "analytic multiplicity to N(X)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effective-li"),
                DeclarationHandle.Create(Owner + ".EffectiveLI"),
                H("Lamzouri's effective linear independence conjecture"),
                StatementSource.FromAuthor(EffectiveLIStatement()),
                AssessedProvenance.FromLiterature(Lamzouri),
                Blocks(Paragraph(Text("Conjecture 1.1 quantifies over every positive exponent "
                    + "slack d. The same positive C applies to every real X ≥ 2 and every nonzero "
                    + "integer coefficient family bounded by N(X). The source counts zeros in "
                    + "[0,X], which agrees with (0,X] for nontrivial zeta zeros under RH since "
                    + "there are no real ones. The conjecture allows C to be ineffective."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eventual-weighted-sine-cutoff-tradeoff"),
                DeclarationHandle.Create(Owner + ".eventual_weighted_sine_cutoff_tradeoff"),
                H("A threshold attained in every window"),
                StatementSource.FromAuthor(TradeoffStatement()),
                AssessedProvenance.FromRepo(Lamzouri),
                Blocks(
                    Paragraph(Text("Write W(h,T) for harmonicMass and S(h,T,v) for weightedSine. "
                        + "Both use the same weight mγ γ/(1/4 + γ²) at each distinct positive "
                        + "ordinate, where mγ is analytic multiplicity. The variables b and e "
                        + "are the window exponent and the allowed normalized loss. The eventual "
                        + "quantifier at positive infinity gives one cutoff above which the "
                        + "bound holds for every T and every interval start a. "),
                        Ref("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine")),
                    Paragraph(Text("Choose 0 < α < min(b,1) and a positive prefix tolerance e₀ "
                        + "such that 2(1 − α²) + α² e₀ < e. Set X = T^α. Normalize the weights "
                        + "through X by W(h,X), use frequencies γ/r and target phase π/2, "
                        + "and fix an integer M with 1/M < e₀. Eventually M ≤ N(X). Effective "
                        + "linear independence then rules out nonzero resonant modes in the "
                        + "coefficient box and bounds their absolute scaled frequencies below "
                        + "by δ = C exp(−X^(1+d))/r. "),
                        Ref("D5/S3/Fourier/WeightedPhaseRecurrence")),
                    Paragraph(Text("Choose d > 0 with α(1+d) < b. The logarithm of the product "
                        + "of the window length and δ is T^b − T^(α(1+d)) + log(C/r). "
                        + "If D is the number of distinct prefix ordinates, D ≤ N(X) because "
                        + "each has multiplicity at least one, and N(X) = O(X log X). "
                        + "Therefore the logarithm of M^D is D log M = O(T^α log T). The "
                        + "positive T^b term eventually dominates both costs and the fixed "
                        + "constants. For R = exp(T^b) the recurrence inequality requires "
                        + "Rδ(e₀ − 1/M) > 2(e₀ M^D − (e₀ − 1/M)). It then gives prefix "
                        + "loss less than e₀ in every interval of length R.")),
                    Paragraph(Text("The common limit of W(h,Y)/log²(Y) as Y tends to infinity is "
                        + "1/(4π). In W(h,T^α)/W(h,T), the two normalized masses have ratio "
                        + "tending to one, while (log(T^α)/log T)² equals α² for T > 1. Thus "
                        + "the retained mass fraction q tends to α². On the omitted band, "
                        + "each sine can contribute loss at most twice its weight. The full "
                        + "normalized loss is less than 2(1 − q) + q e₀, which is eventually "
                        + "less than e by the strict parameter choice.")),
                    Paragraph(Text("The result applies the finite recurrence theorem under RH "
                        + "and Conjecture 1.1 to the actual harmonic weights in every translated "
                        + "time interval of the stated length. Lamzouri's Theorem 1.5 concerns "
                        + "extreme values of Φ at truncation X² over [2,X] on the scale "
                        + "(log log log X)^A, for coefficient sequences satisfying Assumptions "
                        + "1–3 and under ELI."))),
                DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Rh => new Formula.NamedConstant(FormulaIdentifier.Create("RH"));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula OrdinatesStatement()
    {
        var rho = Id("rho");
        var ordinate = Call("Im", rho);
        var realWindow = And(Lt(Num(0), ordinate), Le(ordinate, Id("X")));
        var ordinates = F.Seq(F.OpenBrace, ordinate, F.Sp, F.Mid, F.Sp,
            And(In(rho, Id("Z")), realWindow), F.CloseBrace);
        return F.Disp(All("h", Rh, All("X", Reals, Equal(Call("G", Id("h"), Id("X")), ordinates))));
    }

    private static Formula EffectiveLIStatement()
    {
        var h = Id("h");
        var x = Id("X");
        var d = Id("d");
        var c = Id("C");
        var k = Id("k");
        var j = Id("j");
        var ordinates = Call("G", h, x);
        var coefficient = Call("k", j);
        var coefficients = new Formula.Power(new Formula.Integers(), ordinates);
        var hypotheses = And(Exists("j", ordinates, NotEqual(coefficient, Num(0))),
            All("j", ordinates, Le(new Formula.Absolute(coefficient), Call("N", x))));
        var linearForm = F.Seq(F.Sum, F.Underscore, F.Grp(In(j, ordinates)), F.Sp,
            Multiply(coefficient, j));
        var lowerBound = Multiply(c, Call("exp", new Formula.Negate(new Formula.Power(x, Add(Num(1), d)))));
        var cutoff = All("X", Reals, Imp(Le(Num(2), x), All("k", coefficients,
            Imp(hypotheses, Le(lowerBound, new Formula.Absolute(linearForm))))));
        var bound = All("d", Reals, Imp(Lt(Num(0), d), Exists("C", Reals, And(Lt(Num(0), c), cutoff))));
        return F.Disp(All("h", Rh, new Formula.Logic(Call("ELI", h), FormulaLogicOperator.Iff, bound)));
    }

    private static Formula TradeoffStatement()
    {
        var h = Id("h");
        var r = Id("r");
        var b = Id("b");
        var e = Id("e");
        var t = Id("T");
        var a = Id("a");
        var u = Id("u");
        var mass = Call("W", h, t);
        var cutoffThreshold = Multiply(Num(2),
            Subtract(Num(1), new Formula.Power(Call("min", b, Num(1)), Num(2))));
        var conditions = And(Lt(Num(0), r), And(Lt(Num(0), b), Lt(cutoffThreshold, e)));
        var phase = new Formula.Fraction(u, r);
        var loss = Subtract(Num(1), new Formula.Fraction(Call("S", h, t, phase), mass));
        var endpoint = Add(a, Call("exp", new Formula.Power(t, b)));
        var window = F.Seq(F.OpenBracket, a, F.Comma, F.Sp, endpoint, F.CloseBracket);
        var recurrence = All("a", Reals, Exists("u", Reals, And(In(u, window), Lt(loss, e))));
        var tail = F.Seq(F.Open, t, F.Sp, F.Mapsto, F.Sp, And(Lt(Num(0), mass), recurrence), F.Close);
        var eventually = Call("Eventually", tail, Id("atTop"));
        return F.Disp(All("h", Rh, Imp(Call("ELI", h),
            All("r", Reals, All("b", Reals, All("e", Reals, Imp(conditions, eventually)))))));
    }
}
