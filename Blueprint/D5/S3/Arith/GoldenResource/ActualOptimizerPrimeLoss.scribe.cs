using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ActualOptimizerPrimeLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ActualOptimizerPrimeLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual arbitrary-optimizer weighted prime loss",
        H("Finite arithmetic, directed theta integrals, and same-state payment"),
        Blocks(
            Paragraph(Text("The actual pressure is the attained unrestricted supremum of "
                + "goldenResourceObjective. At every positive original price price b, the "
                + "integer n may be any positive optimizer, with every weak-threshold tie "
                + "choice retained. The finite union of an actual pressure attainer's prime "
                + "support, n's prime support, and the selected band gives the exact full "
                + "objective difference. Original local maximality makes every complementary "
                + "prime gap nonnegative. The original telescoping proof is exposed in place "
                + "in GoldenResourceSupremum and consumed here; it is not re-proved.")),
            Theorem("actual-forward-band-selection", "forward_band_selection",
                "Every forward-band prime is absent", SelectionFormula(true),
                "The band is b<p<=x-1. The original necessary weak thresholds and the strict "
                + "first-layer price bounds force exponent zero. No original equality layer "
                + "is silently assigned to one optimizer."),
            Theorem("actual-reverse-band-selection", "reverse_band_selection",
                "Every reverse-band prime is adopted", SelectionFormula(false),
                "The band is x<p<=b-1. Its upper endpoint remains included, while the "
                + "first-layer profitability at the original price is strict."),
            Theorem("actual-forward-weighted-loss", "forward_weighted_mass_le_defect",
                "The forward weighted sum is paid by the full actual defect", WeightedFormula(true),
                "The weight is log p times (price(p+1)-price x). A locally maximal pressure "
                + "attainer dominates its first-prefix value; the absent original prefix is "
                + "zero. The exact finite objective decomposition retains all complements."),
            Theorem("actual-reverse-weighted-loss", "reverse_weighted_mass_le_defect",
                "The reverse weighted sum is paid by adopted first-layer deficits", WeightedFormula(false),
                "The weight is log p times (price x-price p). The new-price attainer omits "
                + "this prime. Original adoption and decreasing actual layers bound the "
                + "whole adopted prefix by its negative first-layer gain."),
            Paragraph(Text("Finite sum integration identifies the forward sum with the "
                + "integral of curvature(s) times M_F(s) on [b,x], and the reverse sum with "
                + "the integral of curvature(s) times M_R(s) on [x,b]. M_F is exactly "
                + "Chebyshev.theta(s-1)-Chebyshev.theta(b) when s-1>=b, and zero before. "
                + "M_R is exactly Chebyshev.theta(b-1)-Chebyshev.theta(s) when s<=b-1, and "
                + "zero after. Forward atoms activate at p+1; reverse atoms use s<p. Only "
                + "measure-zero integration endpoints are removed, never finite prime atoms. "
                + "The price derivative is minus curvature, and curvature decreases above 1.")),
            Theorem("actual-pressure-defect-theta-charge",
                "actual_optimizer_defect_ge_of_theta_interval_lower",
                "Q uses actual Chebyshev theta and derives every bridge", QFormula(),
                "ThetaIntervalSupplier means (1-epsilon)(v-u)<=Chebyshev.theta(v)-"
                + "Chebyshev.theta(u) for every X<=u<v<=2X with H0<=v-u. Set H=H0+1 and "
                + "rho=(1-epsilon)(1-1/H). On the admitted interval t>=H the actual mass is "
                + "at least rho*t. Integrating only [b+H,x] or [x,b-H] pays rho/2 times "
                + "curvature(max(x,b)) times max((x-b)^2-H^2,0). For distance <=H, including "
                + "equality, the full defect is nonnegative. No selection, charge, weighted "
                + "defect, clock slope, or optimizer-size asymptotic is assumed."),
            Theorem("actual-same-state-reserve-payment", "actual_optimizer_reserve_paid",
                "The actual reserve pays the H-squared loss at A=log n", PaymentFormula(),
                "For X>=25 the actual band (2 sqrt X,4 sqrt X] is a PrimeMask at every "
                + "A in [X,2X]. The pinned ActualReservePrimeMask.actual_reserve_prime_mask "
                + "supplier gives Res(A)>=r_X=1/(8(4 sqrt X+1)log(4 sqrt X)) from the "
                + "displayed actual band-count premise. With omega=curvature(X)H^2/(2r_X), "
                + "Q at x=A pays cH^2 and retains (1-omega)Res(A)+c(A-b)^2, where "
                + "c=rho/2*curvature(max(A,b)). The algebra remains true if omega>1; "
                + "omega<=1 is needed to call its retained reserve coefficient nonnegative. "
                + "The dyadic bounds on A and b remain hypotheses."),
            Paragraph(Text("This attempt preserves source only. No Lean build, kernel check, "
                + "axiom closure, Scribe emission, or registration acceptance is claimed. "
                + "The caller has not supplied the independently verified canonical "
                + "one-thread build mechanism. The inherited Reg source is uncompiled and "
                + "does not cover Q or the paid consumer. Their escape audits remain "
                + "unfinished under the existing linked issue "
                + "https://github.com/the-omega-institute/trureturing/issues/5214. "
                + "The primitive actual-theta and actual band-count suppliers are not "
                + "discharged here. The signed I_psi(log n)+Res(log n)+d_(log n)(n)>0 "
                + "for every n>5040 remains unproved.")))));

    private static DocumentBlock.Describe Theorem(string id, string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula SelectionFormula(bool forward)
    {
        Formula x = F.Id("x"), b = F.Id("b"), n = F.Id("n"), p = F.Id("p");
        return Disp(All([R("x"), R("b"), N("n"), N("p")], Implies(
            AndAll(Lt(D(1), forward ? b : x), Lt(forward ? b : x, forward ? x : b),
                Le(D(1), n), Call("IsGoldenResourceOptimal", Call("price", b), n),
                Call(forward ? "forwardMember" : "reverseMember", p, forward ? b : x, forward ? x : b)),
            forward ? Eq(Call("factorization", n, p), D(0)) : Le(D(1), Call("factorization", n, p)))));
    }

    private static Formula WeightedFormula(bool forward)
    {
        Formula x = F.Id("x"), b = F.Id("b"), n = F.Id("n");
        return Disp(All([R("x"), R("b"), N("n")], Implies(
            AndAll(Lt(D(1), forward ? b : x), Lt(forward ? b : x, forward ? x : b),
                Le(D(1), n), Call("IsGoldenResourceOptimal", Call("price", b), n)),
            Le(Call(forward ? "forwardWeightedMass" : "reverseWeightedMass", forward ? b : x,
                forward ? x : b), Call("actualDefect", x, b, n)))));
    }

    private static Formula QFormula()
    {
        Formula X = F.Id("X"), e = F.Id("epsilon"), H0 = F.Id("H0"), x = F.Id("x"), b = F.Id("b"), n = F.Id("n");
        return Disp(All([R("X"), R("epsilon"), R("H0"), R("x"), R("b"), N("n")], Implies(
            AndAll(Lt(D(1), X), Le(D(0), e), Lt(e, D(1)), Lt(D(0), H0),
                Call("ThetaIntervalSupplier", X, e, H0), Le(X, x), Le(x, Mul(D(2), X)),
                Le(X, b), Le(b, Mul(D(2), X)), Le(D(1), n),
                Call("IsGoldenResourceOptimal", Call("price", b), n)),
            Le(Call("thetaCharge", e, Add(H0, D(1)), x, b), Call("actualDefect", x, b, n)))));
    }

    private static Formula PaymentFormula()
    {
        Formula X = F.Id("X"), e = F.Id("epsilon"), H0 = F.Id("H0"), b = F.Id("b"), n = F.Id("n");
        Formula A = Call("log", n), H = Add(H0, D(1));
        Formula c = Mul(Div(Call("rho", e, H), D(2)), Call("curvature", Call("max", A, b)));
        Formula reserve = Call("actualReserve", A);
        Formula paid = Add(Mul(Sub(D(1), Call("paymentFraction", X, H)), reserve),
            Mul(c, Call("square", Sub(A, b))));
        return Disp(All([R("X"), R("epsilon"), R("H0"), R("b"), N("n")], Implies(
            AndAll(Le(D(25), X), Le(D(0), e), Lt(e, D(1)), Lt(D(0), H0),
                Call("ThetaIntervalSupplier", X, e, H0),
                Le(Div(Mul(D(2), Call("sqrt", X)), Mul(D(2), Call("log", Mul(D(4), Call("sqrt", X))))),
                    Call("card", Call("reserveBand", X))),
                Le(D(1), n), Le(X, A), Le(A, Mul(D(2), X)), Le(X, b), Le(b, Mul(D(2), X)),
                Call("IsGoldenResourceOptimal", Call("price", b), n)),
            Le(paid, Add(reserve, Call("actualDefect", A, b, n))))));
    }

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula.BoundVariable R(string name) => new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("R"))));
    private static Formula.BoundVariable N(string name) => new(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))));
    private static Formula All(Formula.BoundVariable[] vars, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, Grp(b));
    private static Formula AndAll(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
}
