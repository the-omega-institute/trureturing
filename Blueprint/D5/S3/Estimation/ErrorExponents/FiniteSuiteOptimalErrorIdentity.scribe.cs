using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteSuiteOptimalErrorIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ErrorExponents/FiniteSuiteOptimalErrorIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal equal-prior error is determined exactly by total variation, with explicit "
            + "normalization and degeneracy audits.",
        H("Finite-Suite Optimal Error Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-suite-optimal-error-equals-half-one-minus-tv"),
                DeclarationHandle.Create(Prefix + "finite_suite_optimal_error_eq"),
                H("Optimal error equals half of one minus total variation"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The minimum ranges over every decision event on the finite product "
                        + "outcome space. The attaining Le Cam event gives the upper direction, "
                        + "and the eventwise Le Cam inequality gives the lower direction.")),
                    Paragraph(Text(
                        "Only coordinate normalization is required. The nonnegativity clauses "
                            + "from the private source proof do not enter either direction and "
                            + "are therefore omitted from the public statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-normalization-is-necessary"),
                DeclarationHandle.Create(Prefix + "p_normalization_is_necessary"),
                H("First normalization is necessary"),
                StatementSource.FromAuthor(PNormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On Unit indices and Unit outcomes, the zero first law and unit second law "
                        + "give optimal error zero but make the claimed right side one quarter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-normalization-is-necessary"),
                DeclarationHandle.Create(Prefix + "q_normalization_is_necessary"),
                H("Second normalization is necessary"),
                StatementSource.FromAuthor(QNormalizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Swapping the concrete zero and unit laws again gives optimal error zero "
                        + "and right side one quarter, so the second normalization is "
                        + "essential."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-outcome-normalization-is-impossible"),
                DeclarationHandle.Create(
                    Prefix + "empty_outcome_normalization_is_impossible"),
                H("An empty outcome cannot be normalized at a nonempty index"),
                StatementSource.FromAuthor(EmptyOutcomeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the concrete Unit index, a sum over Empty is zero. It therefore "
                        + "cannot satisfy the required unit-mass equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-index-optimal-error-identity"),
                DeclarationHandle.Create(Prefix + "empty_index_optimal_error_eq"),
                H("The identity holds for an empty index"),
                StatementSource.FromAuthor(EmptyIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With no coordinates, normalization is vacuous and both window laws are "
                        + "the same empty product. This remains valid for an empty outcome "
                        + "type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-laws-have-half-error-and-zero-tv"),
                DeclarationHandle.Create(Prefix + "equal_laws_optimal_error_eq"),
                H("Equal laws have half error and zero total variation"),
                StatementSource.FromAuthor(EqualLawsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Identical normalized coordinate laws induce identical product laws. Their "
                        + "total variation is zero and no equal-prior decision beats one half."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula LawType() =>
        new Formula.TypeArrow(F.Id("Index"),
            new Formula.TypeArrow(F.Id("Outcome"), Reals()));

    private static Formula Law(Formula value) =>
        Seq(Open, F.Id("i"), Comma, Sp, F.Id("a"), Close, Sp, Mapsto, Sp, value);

    private static Formula Window(Formula law) => Call("windowLaw", law);

    private static Formula Optimal(Formula first, Formula second) =>
        Call("finiteSuiteOptimalError", first, second);

    private static Formula Tv(Formula first, Formula second) =>
        Call("totalVariation", Window(first), Window(second));

    private static Formula IdentityRight(Formula first, Formula second) =>
        new Formula.Fraction(Seq(D(1), Sp, Minus, Sp, Tv(first, second)), D(2));

    private static Formula Identity(Formula first, Formula second) =>
        new Formula.Relation(
            Optimal(first, second),
            FormulaRelationOperator.Equal,
            IdentityRight(first, second));

    private static Formula Normalized(Formula law) =>
        Seq(Forall, Sp, F.Id("i"), Comma, Sp, Sum, Underscore, Grp(F.Id("a")), Sp,
            Call("eval", law, F.Id("i"), F.Id("a")), Sp, Eq, Sp, D(1));

    private static Formula MainFormula()
    {
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp, LawType(), Comma),
            Seq(Grp(), Normalized(first), Sp, Land, Sp, Normalized(second), Sp, Rightarrow),
            Seq(Identity(first, second))
        ]));
    }

    private static Formula UnitTypes() =>
        Seq(F.Id("Index"), Sp, Eq, Sp, F.Id("Outcome"), Sp, Eq, Sp, F.Id("Unit"));

    private static Formula PNormalizationFormula()
    {
        Formula zero = Law(D(0));
        Formula one = Law(D(1));
        return Disp(Seq(UnitTypes(), Sp, Rightarrow, Sp,
            new Formula.Not(Identity(zero, one))));
    }

    private static Formula QNormalizationFormula()
    {
        Formula zero = Law(D(0));
        Formula one = Law(D(1));
        return Disp(Seq(UnitTypes(), Sp, Rightarrow, Sp,
            new Formula.Not(Identity(one, zero))));
    }

    private static Formula EmptyOutcomeFormula()
    {
        Formula law = F.Id("p");
        Formula type = new Formula.TypeArrow(F.Id("Unit"),
            new Formula.TypeArrow(F.Id("Empty"), Reals()));
        return Disp(Seq(Forall, Sp, law, Colon, Sp, type, Comma, Sp,
            new Formula.Not(Normalized(law))));
    }

    private static Formula EmptyIndexFormula()
    {
        Formula first = F.Id("p");
        Formula second = F.Id("q");
        return Disp(Seq(F.Id("Index"), Sp, Eq, Sp, F.Id("Empty"), Sp,
            Rightarrow, Sp, Identity(first, second)));
    }

    private static Formula EqualLawsFormula()
    {
        Formula law = F.Id("p");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula error = new Formula.Relation(
            Optimal(law, law), FormulaRelationOperator.Equal, half);
        Formula zeroTv = new Formula.Relation(
            Tv(law, law), FormulaRelationOperator.Equal, D(0));
        return Disp(Seq(Normalized(law), Sp, Rightarrow, Sp,
            error, Sp, Land, Sp, zeroTv));
    }
}
