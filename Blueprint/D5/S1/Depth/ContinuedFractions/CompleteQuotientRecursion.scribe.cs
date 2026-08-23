using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class CompleteQuotientRecursionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-step pullbacks make successive quadratic coefficients cross over while "
            + "preserving one discriminant throughout the complete-quotient chain.",
        H("Quadratic Invariants Along Complete Quotients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-next-constant-is-the-current-leading-coefficient"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion."
                        + "next_constant_eq_current_leading"),
                H("The next constant coefficient is the current leading coefficient"),
                StatementSource.FromAuthor(CoefficientCrossoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pulling the current quadratic equation back through the inverse "
                        + "continued-fraction step places its leading coefficient in the "
                        + "constant position of the next equation. This crossover holds at "
                        + "every stage of a compatible quadratic chain."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("every-chain-equation-has-the-initial-discriminant"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion."
                        + "quadratic_chain_discriminant_eq_initial"),
                H("Every chain equation has the initial discriminant"),
                StatementSource.FromAuthor(InitialDiscriminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse-step Mobius transformation has determinant minus one. "
                        + "A pullback scales the discriminant by the determinant squared, "
                        + "so each recurrence step preserves it; induction identifies every "
                        + "stage with the discriminant of the initial equation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("quadratic-chains-share-coefficient-and-discriminant-invariants"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion."
                        + "complete_quotient_quadratic_chain_invariants"),
                H("Quadratic chains share coefficient and discriminant invariants"),
                StatementSource.FromAuthor(ChainInvariantsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every compatible quadratic chain simultaneously has the coefficient "
                            + "crossover at each successor stage and one integral discriminant "
                            + "shared by all its equations. The common value may be chosen as "
                            + "the discriminant of the initial coefficient triple.")),
                    Paragraph(Text(
                        "The result packages invariants of a supplied chain; it does not assert "
                            + "that such a chain exists for every real number."))),
                DescribeRole.Theorem))));

    private static Formula CoefficientCrossoverFormula()
    {
        Formula value = F.Id("x");
        Formula chain = F.Id("C");
        Formula index = F.Id("n");

        return Disp(Seq(
            Forall, Sp, value, Sp, InMacro, Sp, Reals(), Comma, Sp,
            chain, Colon, Sp, QuadraticChain(value), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            Constant(Coefficients(chain, Seq(index, Sp, Plus, Sp, D(1)))),
            Sp, Eq, Sp, Leading(Coefficients(chain, index)), Dot));
    }

    private static Formula InitialDiscriminantFormula()
    {
        Formula value = F.Id("x");
        Formula chain = F.Id("C");
        Formula index = F.Id("n");

        return Disp(Seq(
            Forall, Sp, value, Sp, InMacro, Sp, Reals(), Comma, Sp,
            chain, Colon, Sp, QuadraticChain(value), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma, Esc,
            Discriminant(Coefficients(chain, index)), Sp, Eq, Sp,
            Discriminant(Coefficients(chain, D(0))), Dot));
    }

    private static Formula ChainInvariantsFormula()
    {
        Formula value = F.Id("x");
        Formula chain = F.Id("C");
        Formula index = F.Id("n");
        Formula commonDiscriminant = F.Id("D");

        Formula crossover = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Constant(Coefficients(chain, Seq(index, Sp, Plus, Sp, D(1)))),
            Sp, Eq, Sp, Leading(Coefficients(chain, index)));
        Formula sharedDiscriminant = Seq(
            Exists, Sp, commonDiscriminant, Sp, InMacro, Sp, Integers(), Comma, Sp,
            Forall, Sp, index, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Discriminant(Coefficients(chain, index)), Sp, Eq, Sp,
            commonDiscriminant);

        return Disp(Seq(
            Forall, Sp, value, Sp, InMacro, Sp, Reals(), Comma, Sp,
            chain, Colon, Sp, QuadraticChain(value), Comma, Esc,
            Open, crossover, Close, Sp, Land, Sp,
            Open, sharedDiscriminant, Close, Dot));
    }

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula QuadraticChain(Formula value) =>
        Call("QuadraticChain", value);

    private static Formula Coefficients(Formula chain, Formula index) =>
        Call("coefficients", chain, index);

    private static Formula Leading(Formula coefficients) =>
        Call("leading", coefficients);

    private static Formula Constant(Formula coefficients) =>
        Call("constant", coefficients);

    private static Formula Discriminant(Formula coefficients) =>
        Call("discriminant", coefficients);
}
