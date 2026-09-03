using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class FiniteInversePoissonCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion."
            + "finite_inverse_poisson_rh_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Criticality, positive definiteness, and boundedness are equivalent for a finite "
            + "inverse-Poisson window with explicit functional-equation reflection.",
        H("Finite Inverse-Poisson RH Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-inverse-poisson-rh-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Three equivalent finite-window conditions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite window stores a displacement and ordinate for each term, "
                        + "together with a permutation that negates displacement while "
                        + "preserving ordinate. This makes the functional-equation pairing "
                        + "used by the reverse implication an explicit premise.")),
                Paragraph(Text(
                    "The critical-line implication writes the inverse-Poisson kernel as a "
                        + "finite Gram matrix. Positive semidefiniteness then bounds every "
                        + "value by the value at zero through a two-by-two determinant.")),
                Paragraph(Text(
                    "For the converse, a maximal positive growth rate is normalized out. "
                        + "Bolzano-Weierstrass supplies arbitrarily late simultaneous returns "
                        + "of all finite phases to one, so the nonempty maximal-rate block "
                        + "cannot cancel while the original sum remains bounded.")),
                Paragraph(Text(
                    "The reflection premise is necessary: without it, a one-term window "
                        + "with displacement one and ordinate zero gives exp(-|t|), which is "
                        + "positive definite and bounded but is not on the critical line. "
                        + "The formal module also checks the empty case and a reflected "
                        + "two-point off-line unbounded witness."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula window = F.Id("W");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula windowType = Call("FinitePoissonWindow", n);
        Formula sum = Call("inversePoissonSum", window);
        Formula critical = Call("OnCriticalLine", window);
        Formula positive = Call("PositiveDefinite", sum);
        Formula bounded = Call("BoundedOnReal", sum);
        Formula criticalIffPositive = new Formula.Logic(
            critical,
            FormulaLogicOperator.Iff,
            positive);
        Formula positiveIffBounded = new Formula.Logic(
            positive,
            FormulaLogicOperator.Iff,
            bounded);

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", natural), Bound("W", windowType)],
            new Formula.Logic(
                criticalIffPositive,
                FormulaLogicOperator.And,
                positiveIffBounded));
    }
}
