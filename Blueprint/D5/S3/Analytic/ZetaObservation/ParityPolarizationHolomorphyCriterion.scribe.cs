using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class ParityPolarizationHolomorphyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion."
            + "parity_polarization_holomorphy_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphy of the doubled parity quotient characterizes the zeta zero line.",
        H("Parity Polarization Holomorphy Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("parity-polarization-holomorphy-criterion"),
            DeclarationHandle.Create(Declaration),
            H("The parity quotient is holomorphic exactly on the zero-line criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation region is the open half-plane to the right of one "
                        + "half. Holomorphy means that the literal quotient agrees on each "
                        + "punctured neighborhood with a local analytic germ, so the value "
                        + "assigned at an apparent singularity cannot hide a pole.")),
                Paragraph(Text(
                    "Under the Riemann hypothesis, the zeta residue factorization supplies "
                        + "the required analytic germs, including at one. Conversely, an "
                        + "off-line zero makes the denominator contribute twice its positive "
                        + "multiplicity while the doubled numerator is nonzero, contradicting "
                        + "analyticity of the germ.")),
                Paragraph(Text(
                    "The reciprocal zeta observer has meromorphic order equal to the "
                        + "negative of zeroMult at every zero. This is stronger than limiting "
                        + "the conclusion to off-line zeros and introduces no unused location "
                        + "premise."))),
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
        Formula hasHolomorphicPolarization = F.Id("hasHolomorphicPolarization");
        Formula s = F.Id("s");
        Formula germ = F.Id("germ");
        Formula rho = F.Id("rho");
        Formula multiplicity = F.Id("multiplicity");

        Formula halfPlane = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, complex, F.Sp, F.Mid, F.Sp,
            Fraction(F.D(1), F.D(2)), F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula quotient = Fraction(
            Call("riemannZeta", F.Seq(F.D(2), F.Sp, F.Times, F.Sp, s)),
            Power(Call("riemannZeta", s), F.D(2)));
        Formula reciprocal = Power(Call("riemannZeta", s), F.Seq(F.Minus, F.D(1)));
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
            new Formula.Logic(
                Call("Mem", s, observationHalfPlane),
                FormulaLogicOperator.Implies,
                localGerm));

        Formula zeroPremises = new Formula.Logic(
            Equal(Call("riemannZeta", rho), F.D(0)),
            FormulaLogicOperator.And,
            Equal(Call("zeroMult", rho), multiplicity));
        Formula exactPoleOrder = Equal(
            Call("meromorphicOrderAt", mobiusObserver, rho),
            F.Seq(F.Minus, multiplicity));
        Formula observerClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", complex), Bound("multiplicity", natural)],
            new Formula.Logic(
                zeroPremises,
                FormulaLogicOperator.Implies,
                exactPoleOrder));
        Formula criterion = new Formula.Logic(
            Call("RiemannHypothesis"),
            FormulaLogicOperator.Iff,
            hasHolomorphicPolarization);
        Formula conclusion = new Formula.Logic(
            criterion,
            FormulaLogicOperator.And,
            observerClause);

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
            Let(hasHolomorphicPolarization, proposition, holomorphyAtEveryPoint),
            F.Seq(conclusion, F.Dot),
        ]));
    }

    private static Formula Let(Formula name, Formula type, Formula value) => F.Seq(
        F.Operatorname, F.Grp(F.Id("let")), F.Sp,
        name, F.Colon, F.Sp, type, F.Sp, F.Colon, F.Eq, F.Sp, value, F.Comma);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        F.Seq(F.Open, variable, F.Colon, F.Sp, domain, F.Sp,
            F.Mapsto, F.Sp, body, F.Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
