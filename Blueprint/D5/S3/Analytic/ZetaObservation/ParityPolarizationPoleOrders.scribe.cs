using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ParityPolarizationPoleOrdersDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaObservation/ParityPolarizationPoleOrders."
            + "parity_polarization_holomorphy_and_pole_orders";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The parity quotient criterion carries the exact orders of all three observers.",
        H("Parity Polarization Pole Orders"),
        Blocks(Describe.Lean(
            DescribeId.Create("parity-polarization-pole-orders"),
            DeclarationHandle.Create(Declaration),
            H("Parity holomorphy and the three observer pole orders"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The normalized parity polarization is holomorphic throughout the "
                        + "open observation half-plane exactly when the Riemann hypothesis "
                        + "holds.")),
                Paragraph(Text(
                    "At a zeta zero in that half-plane, doubling moves the numerator into "
                        + "the zero-free half-plane. Meromorphic-order subtraction then gives "
                        + "the multiplicity orders for the reciprocal and Liouville observers "
                        + "and twice that order for the normalized polarization."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula natural = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula proposition = F.Seq(F.Operatorname, F.Grp(F.Id("Prop")));
        Formula observationHalfPlane = F.Id("observationHalfPlane");
        Formula parityPolarization = F.Id("parityPolarization");
        Formula mobiusObserver = F.Id("mobiusObserver");
        Formula liouvilleObserver = F.Id("liouvilleObserver");
        Formula hasHolomorphicPolarization = F.Id("hasHolomorphicPolarization");
        Formula s = F.Id("s");
        Formula germ = F.Id("germ");
        Formula rho = F.Id("rho");
        Formula multiplicity = F.Id("multiplicity");

        Formula halfPlane = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, complex, F.Sp, F.Mid, F.Sp,
            Fraction(F.D(1), F.D(2)), F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula doubledZeta = Call(
            "riemannZeta", F.Seq(F.D(2), F.Sp, F.Times, F.Sp, s));
        Formula zeta = Call("riemannZeta", s);
        Formula quotient = Fraction(doubledZeta, Power(zeta, F.D(2)));
        Formula reciprocal = Power(zeta, F.Seq(F.Minus, F.D(1)));
        Formula liouville = Fraction(doubledZeta, zeta);
        Formula puncturedNeighborhood = Call(
            "nhdsWithin",
            s,
            F.Seq(complex, F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, s, F.CloseBrace));
        Formula analyticExtension = new Formula.Logic(
            Call("AnalyticAt", complex, germ, s),
            FormulaLogicOperator.And,
            Call("EventuallyEq", puncturedNeighborhood, parityPolarization, germ));
        Formula localGerm = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("germ", new Formula.TypeArrow(complex, complex))],
            analyticExtension);
        Formula holomorphyAtEveryPoint = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(Call("Mem", s, observationHalfPlane), localGerm));

        Formula rightSideZeroPremises = And(
            Call("Mem", rho, observationHalfPlane),
            And(
                Equal(Call("riemannZeta", rho), F.D(0)),
                Equal(Call("zeroMult", rho), multiplicity)));
        Formula mobiusOrder = Equal(
            Call("meromorphicOrderAt", mobiusObserver, rho),
            F.Seq(F.Minus, multiplicity));
        Formula liouvilleOrder = Equal(
            Call("meromorphicOrderAt", liouvilleObserver, rho),
            F.Seq(F.Minus, multiplicity));
        Formula polarizationOrder = Equal(
            Call("meromorphicOrderAt", parityPolarization, rho),
            F.Seq(F.Minus, F.D(2), F.Sp, F.Times, F.Sp, multiplicity));
        Formula observerOrders = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex), Bound("multiplicity", natural)],
            Implies(
                rightSideZeroPremises,
                And(mobiusOrder, And(liouvilleOrder, polarizationOrder))));
        Formula criterion = new Formula.Logic(
            Call("RiemannHypothesis"),
            FormulaLogicOperator.Iff,
            hasHolomorphicPolarization);

        return F.Disp(new Formula.Aligned([
            Let(observationHalfPlane, Call("Set", complex), halfPlane),
            Let(
                parityPolarization,
                new Formula.TypeArrow(complex, complex),
                Lambda(s, complex, quotient)),
            Let(
                mobiusObserver,
                new Formula.TypeArrow(complex, complex),
                Lambda(s, complex, reciprocal)),
            Let(
                liouvilleObserver,
                new Formula.TypeArrow(complex, complex),
                Lambda(s, complex, liouville)),
            Let(hasHolomorphicPolarization, proposition, holomorphyAtEveryPoint),
            F.Seq(And(criterion, observerOrders), F.Dot),
        ]));
    }

    private static Formula Let(Formula name, Formula type, Formula value) => F.Seq(
        F.Operatorname, F.Grp(F.Id("let")), F.Sp,
        name, F.Colon, F.Sp, type, F.Sp, F.Colon, F.Eq, F.Sp, value, F.Comma);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        F.Seq(F.Open, variable, F.Colon, F.Sp, domain, F.Sp,
            F.Mapsto, F.Sp, body, F.Close);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
