using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class PtaszynskiThermalHeatKurtosisRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022thermalheat");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact six-state two-bath generator contradicts the proposed nonnegativity of the fourth-to-second scaled heat-current cumulant ratio.",
        H("Negative scaled kurtosis in a thermal Markov current"),
        Blocks(
            Node("totalRate", "Total directed transition rate", TotalRateFormula(),
                "Equation (65), page 6, writes kᵢⱼ = ∑α kᵢⱼᵅ. Here q α i j is the rate from i to j due to bath α, so totalRate q i j sums over the finite bath set Fin L.",
                AssessedProvenance.FromLiterature(Source)),
            Node("ThermalDetailedBalance", "Bath-resolved detailed balance", ThermalFormula(),
                "Equation (66), page 6, states kᵢⱼᵅ/kⱼᵢᵅ = exp(−βᵅ(Eᵢ−Eⱼ)). In directed-rate notation the exponent is β α times (E i − E j). An edge is present exactly when its reverse edge is present, and the ratio equation applies on positive edges. Paired absent edges are allowed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("tiltedRateMatrix", "The heat-tilted generator", TiltedFormula(),
                "Equations (67)–(68), page 6, multiply each off-diagonal contribution from the counted bath by exp(−lambda times (E i − E j)). The diagonal is minus the sum over states k distinct from i of totalRate q i k. The counting field is real and the counted bath belongs to Fin L.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSCGF", "A differentiable characteristic-root branch", ScgfFormula(),
                "Section III D, page 6: “The cumulant generating function χʰ(𝝀) is then equal to the dominant eigenvalue of Wʰ(𝝀) [63]; however, its analytic calculation is usually not possible for N > 4.” Here the branch χ vanishes at zero, is four times continuously differentiable there, and at every real counting field is a greatest real characteristic root of the heat-tilted matrix. Equations (68)–(70) give the characteristic-root equation and derivatives at zero; the root comparison is over real roots, and differentiability is required at zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed nonnegative thermal kurtosis", Disp(Iff(Named("claim"), ClaimBody())),
                "Section III A, item 3, page 3, Eq. (19): “In classical Markovian systems driven only by temperature differences kurtosis of the heat current is always nonnegative”. The displayed inequality is 𝒦ʰ ≥ 0. The carriers are Fin N for states and Fin L for baths; β is strictly positive, the directed rates are nonnegative off the diagonal and satisfy bath-resolved detailed balance. The assertion includes existence of a branch and requires the ratio to be nonnegative for every such branch with positive second derivative. Equations (4) and (10), page 2, define this ratio using scaled cumulants: iteratedDeriv 4 χ 0 divided by iteratedDeriv 2 χ 0. It is not the standardized fourth central moment.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("ptkurt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A six-state refutation"), StatementSource.FromAuthor(Disp(Not(ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take six alternating energy levels (0, 1, 0, 1, 0, 1), with inverse temperatures log 2 and log 8. The first bath joins each consecutive low–high pair with forward rates (1, 6, 6) and reverse rates (2, 12, 12). The second bath joins each high level to the next low level cyclically with downhill rate 8 and reverse rate 1. Counting the second bath gives det(z I − W(t)) = 63504 z + 50202 z² + 13968 z³ + 1507 z⁴ + 66 z⁵ + z⁶ − 18432(exp(3t) − 1) − 288(exp(−3t) − 1). Every branch supplied by the assertion has second derivative 3581/2401 and fourth derivative −113056891/1129900996 at zero. Their ratio is −113056891/1685204276, contradicting nonnegativity. The proof uses the asserted existence of a branch and its characteristic-root equation; it does not separately establish existence or identify a Perron eigenvalue."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("ptkurt-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, Parenthesized(body));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Negate(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", Parenthesized(c), a, b);
    private static Formula MatrixType(Formula n) => Call("Matrix", Fin(n), Fin(n), Real());
    private static Formula RatesType(Formula n, Formula l) => Arrow(Fin(l), Arrow(Fin(n), Arrow(Fin(n), Real())));
    private static Formula FiniteSum(string name, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(F.Id(name), Colon, type), Sp, body);
    private static Formula EnergyType(Formula n) => Arrow(Fin(n), Real());
    private static Formula WithParameters(Formula body) => All("N", Nat(), All("L", Nat(), body));

    private static Formula TotalRateFormula()
    {
        Formula n = F.Id("N"), l = F.Id("L"), q = F.Id("q"), i = F.Id("i"), j = F.Id("j"), a = F.Id("a");
        return Disp(WithParameters(All("q", RatesType(n, l), All("i", Fin(n), All("j", Fin(n),
            Equal(Call("totalRate", q, i, j), FiniteSum("a", Fin(l), App(q, a, i, j))))))));
    }

    private static Formula ThermalFormula()
    {
        Formula n = F.Id("N"), l = F.Id("L"), e = F.Id("E"), b = F.Id("b"), q = F.Id("q");
        Formula a = F.Id("a"), i = F.Id("i"), j = F.Id("j");
        Formula forward = App(q, a, i, j), reverse = App(q, a, j, i);
        Formula law = Equal(new Formula.Fraction(forward, reverse),
            QCall("Real", "exp", Mul(App(b, a), Parenthesized(Sub(App(e, i), App(e, j))))));
        Formula body = All("a", Fin(l), All("i", Fin(n), All("j", Fin(n),
            Imp(Not(Equal(i, j)), And(Iff(Less(D(0), forward), Less(D(0), reverse)), Imp(Less(D(0), forward), law))))));
        return Disp(WithParameters(All("E", EnergyType(n), All("b", EnergyType(l), All("q", RatesType(n, l),
            Iff(Call("ThermalDetailedBalance", e, b, q), body))))));
    }

    private static Formula TiltedFormula()
    {
        Formula n = F.Id("N"), l = F.Id("L"), e = F.Id("E"), q = F.Id("q"), a = F.Id("a"), c = F.Id("c");
        Formula t = F.Id("t"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula factor = Ite(Equal(a, c), QCall("Real", "exp", Mul(Negate(t), Parenthesized(Sub(App(e, i), App(e, j))))), D(1));
        Formula body = Ite(Not(Equal(i, j)), FiniteSum("a", Fin(l), Mul(App(q, a, j, i), factor)), Negate(FiniteSum("k", Fin(n), Ite(Equal(k, i), D(0), Call("totalRate", q, i, k)))));
        return Disp(WithParameters(All("E", EnergyType(n), All("q", RatesType(n, l), All("c", Fin(l), All("t", Real(),
            All("i", Fin(n), All("j", Fin(n), Equal(App(Call("tiltedRateMatrix", e, q, c, t), i, j), body)))))))));
    }

    private static Formula Characteristic(Formula n, Formula a, Formula z) => QCall("Matrix", "det",
        Parenthesized(Sub(QCall("HSMul", "hSMul", z, Parenthesized(Seq(D(1), Colon, MatrixType(n)))), a)));

    private static Formula ScgfFormula()
    {
        Formula n = F.Id("N"), l = F.Id("L"), e = F.Id("E"), q = F.Id("q"), c = F.Id("c"), f = F.Id("f"), t = F.Id("t");
        Formula body = And(Equal(App(f, D(0)), D(0)), And(Call("ContDiffAt", Real(), D(4), f, D(0)),
            All("t", Real(), And(Equal(Characteristic(n, Call("tiltedRateMatrix", e, q, c, t), App(f, t)), D(0)),
                All("v", Real(), Imp(Equal(Characteristic(n, Call("tiltedRateMatrix", e, q, c, t), F.Id("v")), D(0)), Leq(F.Id("v"), App(f, t))))))));
        return Disp(WithParameters(All("E", EnergyType(n), All("q", RatesType(n, l), All("c", Fin(l),
            All("f", Arrow(Real(), Real()), Iff(Call("IsSourceSCGF", e, q, c, f), body)))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N"), l = F.Id("L"), e = F.Id("E"), b = F.Id("b"), q = F.Id("q"), c = F.Id("c"), f = F.Id("f");
        Formula a = F.Id("a"), i = F.Id("i"), j = F.Id("j");
        Formula scgf = Call("IsSourceSCGF", e, q, c, f);
        Formula second = Call("iteratedDeriv", D(2), f, D(0));
        Formula fourth = Call("iteratedDeriv", D(4), f, D(0));
        Formula conclusion = And(Some("f", Arrow(Real(), Real()), scgf), All("f", Arrow(Real(), Real()),
            Imp(scgf, Imp(Less(D(0), second), Leq(D(0), new Formula.Fraction(fourth, second))))));
        Formula body = Imp(All("a", Fin(l), Less(D(0), App(b, a))),
            Imp(All("a", Fin(l), All("i", Fin(n), All("j", Fin(n), Imp(Not(Equal(i, j)), Leq(D(0), App(q, a, i, j)))))),
                Imp(Call("ThermalDetailedBalance", e, b, q), conclusion)));
        return WithParameters(All("E", EnergyType(n), All("b", EnergyType(l), All("q", RatesType(n, l), All("c", Fin(l), body)))));
    }
}
