using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaObservation;

internal sealed class LiouvilleParityHolomorphyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/ZetaObservation/LiouvilleParityHolomorphyCriterion."
            + "liouville_parity_holomorphy_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphy of the Liouville parity quotient characterizes the zeta zero line.",
        H("Liouville Parity Holomorphy Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("liouville-parity-holomorphy-criterion"),
            DeclarationHandle.Create(Declaration),
            H("The Liouville parity quotient is holomorphic exactly on the zero-line criterion"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation region is the open half-plane to the right of one "
                        + "half. Holomorphy means that the literal quotient agrees on each "
                        + "punctured neighborhood with a local analytic germ, so the value "
                        + "assigned at an apparent singularity cannot hide a pole.")),
                Paragraph(Text(
                    "The Riemann hypothesis removes denominator zeros from the open "
                        + "half-plane, while the zeta residue factorization supplies an "
                        + "analytic germ at one. Conversely, an off-line zero contributes "
                        + "positive denominator multiplicity while the doubled numerator "
                        + "is nonzero, contradicting analyticity of the local germ."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula complex = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula proposition = F.Seq(F.Operatorname, F.Grp(F.Id("Prop")));
        Formula observationHalfPlane = F.Id("observationHalfPlane");
        Formula liouvilleParity = F.Id("liouvilleParity");
        Formula hasHolomorphicParity = F.Id("hasHolomorphicParity");
        Formula s = F.Id("s");
        Formula germ = F.Id("germ");

        Formula halfPlane = F.Seq(
            F.OpenBrace, s, F.InMacro, F.Sp, complex, F.Sp, F.Mid, F.Sp,
            Fraction(F.D(1), F.D(2)), F.Sp, F.Lt, F.Sp,
            F.Re, F.Open, s, F.Close, F.CloseBrace);
        Formula quotient = Fraction(
            Call("riemannZeta", F.Seq(F.D(2), F.Sp, F.Times, F.Sp, s)),
            Call("riemannZeta", s));
        Formula puncturedNeighborhood = Call(
            "nhdsWithin",
            s,
            F.Seq(complex, F.Sp, F.Setminus, F.Sp,
                F.OpenBrace, s, F.CloseBrace));
        Formula analyticExtension = new Formula.Logic(
            Call("AnalyticAt", complex, germ, s),
            FormulaLogicOperator.And,
            Call("EventuallyEq", puncturedNeighborhood, liouvilleParity, germ));
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
        Formula criterion = new Formula.Logic(
            Call("RiemannHypothesis"),
            FormulaLogicOperator.Iff,
            hasHolomorphicParity);

        return F.Disp(new Formula.Aligned([
            Let(observationHalfPlane, Call("Set", complex), halfPlane),
            Let(
                liouvilleParity,
                new Formula.TypeArrow(complex, complex),
                Lambda(s, complex, quotient)),
            Let(hasHolomorphicParity, proposition, holomorphyAtEveryPoint),
            F.Seq(criterion, F.Dot),
        ]));
    }

    private static Formula Let(Formula name, Formula type, Formula value) => F.Seq(
        F.Operatorname, F.Grp(F.Id("let")), F.Sp,
        name, F.Colon, F.Sp, type, F.Sp, F.Colon, F.Eq, F.Sp, value, F.Comma);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        F.Seq(F.Open, variable, F.Colon, F.Sp, domain, F.Sp,
            F.Mapsto, F.Sp, body, F.Close);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
