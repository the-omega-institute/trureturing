using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class UnconditionalExplicitFormulaDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/UnconditionalExplicitFormula.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical explicit formula and prime-archimedean energy identity hold for "
            + "every repository Weil test function without separate convergence hypotheses, "
            + "and below the first prime power the Poincare target reduces to its "
            + "archimedean part.",
        H("Unconditional Explicit Formula"),
        Blocks(
            Paragraph(Text(
                "The explicit formula and the energy decomposition are frozen theorems of "
                    + "this repository; the latter was supplied by another driver. They are "
                    + "only de-hypothesized here through the frozen W-12 archimedean "
                    + "convergence theorem and the frozen M2-c symmetric convergence theorem.")),
            Paragraph(Text(
                "The analytic identities are relative to supplied ZeroData only. Existence "
                    + "of ZeroData is not asserted, and M1-b remains open. Every test function "
                    + "below is this repository's WeilTestFunction.")),
            Paragraph(Text(
                "The small-support theorem is only a reduction: it does not assert the "
                    + "reduced archimedean inequality, which remains the open target of the "
                    + "ZetaGamma line. None of these statements is a proof of the Riemann "
                    + "hypothesis.")),
            Describe.Lean(
                DescribeId.Create("explicit-formula-unconditional"),
                DeclarationHandle.Create(Prefix + "explicitFormula_unconditional"),
                H("The explicit formula without convergence hypotheses"),
                StatementSource.FromAuthor(ExplicitFormulaStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The symmetric and archimedean convergence arguments are the canonical "
                        + "witnesses supplied by M2-c and W-12, respectively."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("energy-identity-unconditional"),
                DeclarationHandle.Create(Prefix + "energyIdentity_unconditional"),
                H("The prime-archimedean energy identity without convergence hypotheses"),
                StatementSource.FromAuthor(EnergyIdentityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The support hypothesis is unchanged. Only the two convergence premises "
                        + "of the frozen decomposition are discharged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-support-poincare-reduction"),
                DeclarationHandle.Create(Prefix + "smallSupport_poincare_reduction"),
                H("Small support removes the arithmetic prime-power energy"),
                StatementSource.FromAuthor(SmallSupportReductionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The strict threshold exp(2L) < 2 makes activePrimePowers(L) empty, so "
                        + "both totalPrimeWeight(L) and arithmeticJumpEnergy(L,f) vanish."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ExplicitFormulaStatement()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("g");
        Formula zeroWitness = Call("symmetricConvergentOfZeroData", zeros, test);
        Formula archWitness = Call("archimedeanConvergentOfWeilTestFunction", test);
        Formula zeroSide = Call("zeroSum", zeros, test, zeroWitness);
        Formula primeSide = Add(
            Subtract(Call("poleTerm", test), Call("primeTerm", test)),
            Call("archimedeanTerm", test, archWitness));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData")), Bound("g", F.Id("WeilTestFunction"))],
            Equal(zeroSide, primeSide)));
    }

    private static Formula EnergyIdentityStatement()
    {
        Formula zeros = F.Id("Z");
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula square = Call("convolutionSquare", test);
        Formula support = SupportCondition(test, scale);
        Formula zeroWitness = Call("symmetricConvergentOfZeroData", zeros, square);
        Formula zeroSide = Call("zeroSum", zeros, square, zeroWitness);

        return Disp(ForAll(
            [
                Bound("Z", F.Id("ZeroData")),
                Bound("f", F.Id("WeilTestFunction")),
                Bound("L", Reals()),
                Bound("hSupport", support),
            ],
            Equal(zeroSide, FullEnergy(test, scale))));
    }

    private static Formula SmallSupportReductionStatement()
    {
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula threshold = LessThan(
            Call("exp", Multiply(D(2), scale)), D(2));
        Formula fullInequality = LessOrEqual(
            FullThreshold(test, scale), FullPositiveEnergy(test, scale));
        Formula reducedInequality = LessOrEqual(
            ReducedThreshold(test), ReducedPositiveEnergy(test));

        return Disp(ForAll(
            [
                Bound("f", F.Id("WeilTestFunction")),
                Bound("L", Reals()),
                Bound("hL", threshold),
            ],
            Iff(fullInequality, reducedInequality)));
    }

    private static Formula FullEnergy(Formula test, Formula scale) =>
        Subtract(FullPositiveEnergy(test, scale), FullThreshold(test, scale));

    private static Formula FullPositiveEnergy(Formula test, Formula scale) =>
        Add(
            Add(BoundaryEnergy(test), Call("archimedeanJumpEnergy", test)),
            Call("arithmeticJumpEnergy", scale, test));

    private static Formula ReducedPositiveEnergy(Formula test) =>
        Add(BoundaryEnergy(test), Call("archimedeanJumpEnergy", test));

    private static Formula FullThreshold(Formula test, Formula scale) =>
        Multiply(
            Subtract(
                Multiply(D(2), Call("totalPrimeWeight", scale)),
                ArchimedeanConstant()),
            Call("l2Mass", test));

    private static Formula ReducedThreshold(Formula test) =>
        Multiply(Seq(Minus, ArchimedeanConstant()), Call("l2Mass", test));

    private static Formula BoundaryEnergy(Formula test) =>
        Multiply(D(2), Call("normSq", BoundaryIntegral(test)));

    private static Formula BoundaryIntegral(Formula test)
    {
        Formula variable = F.Id("x");
        Formula integrand = Multiply(
            Call("exp", new Formula.Fraction(variable, D(2))),
            Call("f", variable));
        return Seq(
            Int, Underscore, Grp(Reals()), Sp,
            integrand, Sp, F.Id("d"), variable);
    }

    private static Formula SupportCondition(Formula test, Formula scale) =>
        SubsetOrEqual(
            Call("tsupport", test),
            Seq(OpenBracket, Seq(Minus, scale), Comma, Sp, scale, CloseBracket));

    private static Formula ArchimedeanConstant() =>
        Seq(Operatorname, Grp(F.Id("archimedeanConstant")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(
            left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula SubsetOrEqual(Formula left, Formula right) =>
        new Formula.Relation(
            left, FormulaRelationOperator.SubsetOf, right);
}
