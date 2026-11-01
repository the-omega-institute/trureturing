using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class IntervalLInfinityRepresentativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Internal essential-supremum translations produce unique continuous representatives with a common modulus on a closed interval.",
        H("Continuous representatives from internal L-infinity translations"),
        Blocks(
            Paragraph(Text("Throughout, E is a real Banach space in any universe. Ioc(a,b) is the right-closed interval (a,b], and Icc(a,b) is the closed interval [a,b]. RestrictedVolume denotes restricted Lebesgue measure. Average(f,A) is the Bochner integral of f over A divided by its measure. InternalDifference(f,h) is the function t mapped to f(t+h)-f(t). AEEq(mu,f,g) means equality of the two functions almost everywhere for mu. The projection projIcc(0,T,t) clamps t to [0,T] and takes values in that closed-interval subtype. IccExtend(g,0,T) is the real-line function t mapped to g(projIcc(0,T,t)).")),
            Describe.Lean(DescribeId.Create("local-average-consistency"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/IntervalLInfinityRepresentative.local_average_consistency"),
                H("Consistency of arbitrary short interval averages"),
                StatementSource.FromAuthor(F.Disp(AverageStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f be strongly measurable on the real line and integrable on Ioc(0,T). Suppose every positive internal translation below delta has L-infinity seminorm less than ofReal(epsilon), where epsilon is nonnegative. Consider any two positive-length interval windows Ioc(a,b) and Ioc(c,d) contained in Ioc(0,T). If every point of one window has distance less than delta from every point of the other, then the distance of their averages is at most epsilon. The windows may have different lengths, overlap, or meet either endpoint of the original interval.")),
                    Paragraph(Text("For each fixed shift the essential-supremum estimate holds outside a null set. Fubini's theorem and the measure-preserving shear (x,h) mapped to (x,x+h) give the corresponding estimate for almost every pair of times. Symmetry covers negative separations, and the diagonal has zero difference. Restricting that pair estimate to the product of the two windows and applying Mathlib's convex-set average theorem twice proves the average estimate. There is no intersection over uncountably many shift-dependent sets.")))),
            Describe.Lean(DescribeId.Create("continuous-representatives"),
                DeclarationHandle.Create("D5/S3/Topology/Measures/IntervalLInfinityRepresentative.exists_continuous_representatives"),
                H("A common modulus for the unique continuous representatives"),
                StatementSource.FromAuthor(F.Disp(RepresentativeStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("T is positive and S is an arbitrary, possibly empty subset of the actual Lp(E,infinity,RestrictedVolume(Ioc(0,T))) space. The translation scale is uniform over S. The map R has domain S itself and codomain the continuous maps on Icc(0,T). The first conclusion identifies each original almost-everywhere class. The second gives one epsilon-delta continuity condition for all members and all pairs of points, including 0 and T. The third gives uniqueness among all continuous representatives. The fourth permits every almost-everywhere equal real-line representative u, preserving both its identification with R(f) and every positive internal translation seminorm.")),
                    Paragraph(Text("For x in [0,T] and r>0, take the average over Ioc(max(0,x-r),min(T,x+r)). This window has positive length even at x=0 or x=T. With r=1/(n+1), the consistency estimate makes these averages Cauchy. Completeness of E gives a limit at every x. The same estimate for windows centered at nearby points passes to the limits and supplies a common continuity modulus. For each of the countably many accuracies 1/(k+1), the pair estimate also makes the shrinking averages close to f(x) for almost every x. Passing to their limits identifies the continuous function with the original class. Full support of Lebesgue measure on the interval and continuity then give uniqueness.")),
                    Paragraph(Text("There is no separate common bound on the norms of S, no restriction on the dimension of E, and no separability or reflexivity assumption. The integral construction uses only the individual integrability inherited from L-infinity on a finite interval. It assumes no pointwise time modulus, continuous representative, endpoint value, boundary-tail condition, or whole-line translation estimate. In particular the unbounded family of all scalar constant functions satisfies the translation condition and has a common continuity modulus; this assertion does not claim that such a family is compact.")),
                    Paragraph(Text("Simon, Compact sets in the space Lp(0,T;B), DOI 10.1007/BF01762360, Section 3, Theorem 1, includes a compactness conclusion in C(0,T;B) for p=infinity and uses right means and opposite time directions. Its C convention uses the closed interval. That source does not separately state the entire arbitrary-family lifting and uniqueness assertion displayed here. The present local-window construction is a derived argument; no originality or open-problem claim is made.")))))));

    private static Formula AverageStatement()
    {
        var e = Id("E"); var f = Id("f"); var t = Id("T");
        var delta = Id("delta"); var eps = Id("epsilon");
        var a = Id("a"); var b = Id("b"); var c = Id("c"); var d = Id("d");
        var x = Id("x"); var y = Id("y");
        var close = All("x", Id("Real"), All("y", Id("Real"),
            Implies(And(Member(x, Ioc(a, b)), Member(y, Ioc(c, d))),
                Lt(Call("abs", Call("sub", y, x)), delta))));
        var premises = And(Call("RealBanach", e), Call("StronglyMeasurable", f),
            Call("IntegrableOn", f, Ioc(F.D(0), t)), Le(F.D(0), eps),
            Shifts(f, t, delta, eps), Le(F.D(0), a), Lt(a, b), Le(b, t),
            Le(F.D(0), c), Lt(c, d), Le(d, t), close);
        var conclusion = Le(Call("dist", Call("Average", f, Ioc(a, b)),
            Call("Average", f, Ioc(c, d))), eps);
        return All("E", Id("Types"), All("f", new Formula.TypeArrow(Id("Real"), e),
            All("T", Id("Real"), All("delta", Id("Real"), All("epsilon", Id("Real"),
            All("a", Id("Real"), All("b", Id("Real"), All("c", Id("Real"),
            All("d", Id("Real"), Implies(premises, conclusion))))))))));
    }

    private static Formula RepresentativeStatement()
    {
        var e = Id("E"); var t = Id("T"); var s = Id("S"); var r = Id("R");
        var f = Id("f"); var u = Id("u"); var g = Id("g"); var h = Id("h");
        var eps = Id("epsilon"); var delta = Id("delta"); var eta = Id("eta");
        var x = Id("x"); var y = Id("y");
        var interval = Call("Icc", F.D(0), t);
        var mu = Volume(Ioc(F.D(0), t));
        var lp = Call("Lp", e, F.Infty, mu);
        var continuous = Call("ContinuousMap", interval, e);
        var translations = All("epsilon", Id("Real"), Implies(Lt(F.D(0), eps),
            Exists("delta", Id("Real"), And(Lt(F.D(0), delta),
                All("f", lp, Implies(Member(f, s), Shifts(f, t, delta, eps)))))));
        var representative = All("f", s, AEEq(mu, Extend(Call("R", f), t), f));
        var modulus = All("epsilon", Id("Real"), Implies(Lt(F.D(0), eps),
            Exists("eta", Id("Real"), And(Lt(F.D(0), eta), All("f", s,
                All("x", interval, All("y", interval,
                    Implies(Lt(Call("dist", x, y), eta),
                        Lt(Call("dist", Call("R", f, x), Call("R", f, y)), eps)))))))));
        var unique = All("f", s, All("g", continuous,
            Implies(AEEq(mu, Extend(g, t), f), Eq(g, Call("R", f)))));
        var invariant = All("f", s, All("u", new Formula.TypeArrow(Id("Real"), e),
            Implies(AEEq(mu, u, f), And(AEEq(mu, Extend(Call("R", f), t), u),
                All("h", Id("Real"), Implies(And(Lt(F.D(0), h), Lt(h, t)),
                    Eq(IncrementNorm(u, t, h), IncrementNorm(f, t, h))))))));
        var conclusion = Exists("R", new Formula.TypeArrow(s, continuous),
            And(representative, modulus, unique, invariant));
        return All("E", Id("Types"), All("T", Id("Real"), All("S", Call("Set", lp),
            Implies(And(Call("RealBanach", e), Lt(F.D(0), t), translations), conclusion))));
    }

    private static Formula Shifts(Formula f, Formula t, Formula delta, Formula eps) =>
        All("h", Id("Real"), Implies(And(Lt(F.D(0), Id("h")), Lt(Id("h"), delta),
            Lt(Id("h"), t)), Lt(IncrementNorm(f, t, Id("h")), Call("ofReal", eps))));
    private static Formula IncrementNorm(Formula f, Formula t, Formula h) =>
        Call("eLpNorm", Call("InternalDifference", f, h), F.Infty,
            Volume(Ioc(F.D(0), Call("sub", t, h))));
    private static Formula Extend(Formula f, Formula t) =>
        Call("IccExtend", f, F.D(0), t);
    private static Formula AEEq(Formula mu, Formula f, Formula g) => Call("AEEq", mu, f, g);
    private static Formula Ioc(Formula a, Formula b) => Call("Ioc", a, b);
    private static Formula Volume(Formula domain) => Call("RestrictedVolume", domain);
    private static Formula Member(Formula x, Formula s) => Call("Member", x, s);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Exists(string s, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] clauses)
    {
        var r = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            r = new Formula.Logic(clauses[i], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
