using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GammaThermal;

internal sealed class ArchimedeanQuarterPairThermalEnvelopeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two quarter-shifted Archimedean Gamma channels have an exact thermal envelope.",
        H("Archimedean Quarter-Pair Thermal Envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("archimedean-quarter-pair-thermal-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GammaThermal/ArchimedeanQuarterPairThermalEnvelope."
                        + "archimedean_quarter_pair_thermal_envelope"),
                H("The quarter-pair Gamma product has a Fermi-like thermal envelope"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t, the first conjunct gives the squared-norm product "
                            + "of Gamma(1/4 + it/2) and Gamma(3/4 + it/2) as "
                            + "2 pi^2 / cosh(pi t). The second conjunct gives exactly the "
                            + "reciprocal-cosh exponential identity with |t|. The third "
                            + "conjunct combines them into the concrete pair's exact "
                            + "Fermi-like exponential envelope.")),
                    Paragraph(Text(
                        "The proof specializes the pinned Gamma duplication and reflection "
                            + "identities, then rewrites the hyperbolic cosine using real "
                            + "exponentials. It uses no Riemann-hypothesis assumption."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Multiply(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Seq(Open, value, Close), D(2));

    private static Formula TheoremFormula()
    {
        Formula real = Call("Real");
        Formula t = F.Id("t");
        Formula imaginaryUnit = F.Id("i");
        Formula piTimesT = Multiply(Pi, t);
        Formula gammaPlus = Call(
            "Gamma",
            Seq(
                new Formula.Fraction(D(1), D(4)), Sp, Plus, Sp,
                Multiply(imaginaryUnit, new Formula.Fraction(t, D(2)))));
        Formula gammaMinus = Call(
            "Gamma",
            Seq(
                new Formula.Fraction(D(3), D(4)), Sp, Plus, Sp,
                Multiply(imaginaryUnit, new Formula.Fraction(t, D(2)))));
        Formula cosh = Call("cosh", piTimesT);
        Formula normProduct = Multiply(
            Square(new Formula.Absolute(gammaPlus)),
            Square(new Formula.Absolute(gammaMinus)));
        Formula firstRight = new Formula.Fraction(
            Multiply(D(2), Square(Pi)),
            cosh);
        Formula first = EqualTo(normProduct, firstRight);
        Formula absoluteT = new Formula.Absolute(t);
        Formula negativePiAbsoluteT = Seq(Minus, Multiply(Pi, absoluteT));
        Formula negativeTwoPiAbsoluteT =
            Seq(Minus, Multiply(D(2), Multiply(Pi, absoluteT)));
        Formula secondNumerator = Multiply(
            D(2),
            Call("exp", negativePiAbsoluteT));
        Formula secondDenominator = Seq(
            D(1), Sp, Plus, Sp, Call("exp", negativeTwoPiAbsoluteT));
        Formula second = EqualTo(
            new Formula.Fraction(D(1), cosh),
            new Formula.Fraction(secondNumerator, secondDenominator));
        Formula third = EqualTo(
            normProduct,
            Multiply(
                Multiply(D(2), Square(Pi)),
                new Formula.Fraction(secondNumerator, secondDenominator)));
        Formula conclusion = new Formula.Logic(
            first,
            FormulaLogicOperator.And,
            new Formula.Logic(second, FormulaLogicOperator.And, third));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("t", real)],
            conclusion));
    }
}
