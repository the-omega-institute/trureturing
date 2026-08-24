using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FiniteIdentificationCapacityBoundDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Injective joint readout bounds a finite state space by the capacity of its dependent "
            + "outcome space, equivalently by its base-two logarithmic cost at positive capacity.",
        H("Finite Identification Capacity Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("injective-joint-readout-bounds-state-cardinality"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_identification_capacity_bound"),
                H("Injective joint readout bounds state cardinality"),
                StatementSource.FromAuthor(CapacityBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite experiment family, capacity is the number of dependent "
                            + "joint outcome tuples, with one outcome chosen from each indexed "
                            + "outcome type.")),
                    Paragraph(Text(
                        "An injective joint readout assigns different tuples to different states. "
                            + "The finite state space therefore embeds in the joint-outcome space, "
                            + "so its cardinality cannot exceed the experiment capacity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("capacity-bound-implies-base-two-cost-bound"),
                DeclarationHandle.Create(DeclarationPrefix + "cost_form"),
                H("The capacity bound implies the base-two cost bound"),
                StatementSource.FromAuthor(CostBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When capacity is positive, the injective readout first gives the finite "
                            + "cardinality bound. Taking logarithms to base two preserves that "
                            + "order, and the logarithm of capacity is exactly the defined cost.")),
                    Paragraph(Text(
                        "If the state cardinality is zero, its base-two logarithm is zero and the "
                            + "positive capacity has nonnegative cost. Otherwise both cardinalities "
                            + "are positive, so ordinary logarithmic monotonicity applies directly."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("positive-capacity-equates-cardinal-and-cost-bounds"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "cardinal_bound_iff_cost_bound"),
                H("Positive capacity equates cardinal and cost bounds"),
                StatementSource.FromAuthor(BoundEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At positive capacity, bounding the number of states by the joint-readout "
                            + "capacity is equivalent to bounding its base-two logarithm by the "
                            + "identification cost.")),
                    Paragraph(Text(
                        "The forward implication is monotonicity of the base-two logarithm. For a "
                            + "nonempty finite state space, strict increase of that logarithm also "
                            + "reflects the cost inequality back to the cardinal inequality; the "
                            + "zero-cardinality case satisfies the cardinal bound automatically."))),
                DescribeRole.Lemma))));

    private static Formula CapacityBoundFormula()
    {
        Formula state = F.Id("X");
        Formula index = F.Id("J");
        Formula outcome = F.Id("O");
        Formula readout = F.Id("qJ");
        Formula coordinate = F.Id("j");
        Formula outcomeAtCoordinate = new Formula.Subscript(outcome, coordinate);
        Formula jointOutcomes = Seq(
            Prod, Underscore, Grp(coordinate, Colon, Sp, index), outcomeAtCoordinate);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, index, Colon, Sp, TypeUniverse(), Comma, Sp,
                outcome, Colon, Sp, index, Sp, To, Sp, TypeUniverse(), Comma),
            Seq(
                readout, Colon, Sp, Arrow(state, jointOutcomes), Comma),
            Seq(
                FiniteFamilyAssumptions(state, index, outcome, coordinate), Sp, Land, Sp,
                Call("Injective", readout), Sp, Rightarrow, Sp,
                Card(state), Sp, Leq, Sp, Capacity(outcome), Dot),
        ]));
    }

    private static Formula CostBoundFormula()
    {
        Formula state = F.Id("X");
        Formula index = F.Id("J");
        Formula outcome = F.Id("O");
        Formula readout = F.Id("qJ");
        Formula coordinate = F.Id("j");
        Formula outcomeAtCoordinate = new Formula.Subscript(outcome, coordinate);
        Formula jointOutcomes = Seq(
            Prod, Underscore, Grp(coordinate, Colon, Sp, index), outcomeAtCoordinate);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, index, Colon, Sp, TypeUniverse(), Comma, Sp,
                outcome, Colon, Sp, index, Sp, To, Sp, TypeUniverse(), Comma),
            Seq(
                readout, Colon, Sp, Arrow(state, jointOutcomes), Comma),
            Seq(
                FiniteFamilyAssumptions(state, index, outcome, coordinate), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, Capacity(outcome), Sp, Land, Sp,
                Call("Injective", readout), Sp, Rightarrow, Sp,
                LogCardinality(state), Sp, Leq, Sp, Cost(outcome), Dot),
        ]));
    }

    private static Formula BoundEquivalenceFormula()
    {
        Formula state = F.Id("X");
        Formula index = F.Id("J");
        Formula outcome = F.Id("O");
        Formula coordinate = F.Id("j");

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, index, Colon, Sp, TypeUniverse(), Comma, Sp,
                outcome, Colon, Sp, index, Sp, To, Sp, TypeUniverse(), Comma),
            Seq(
                FiniteFamilyAssumptions(state, index, outcome, coordinate), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, Capacity(outcome), Sp, Rightarrow, Sp),
            Seq(
                Open, Card(state), Sp, Leq, Sp, Capacity(outcome), Sp,
                Iff, Sp, LogCardinality(state), Sp, Leq, Sp, Cost(outcome), Close, Dot),
        ]));
    }

    private static Formula FiniteFamilyAssumptions(
        Formula state, Formula index, Formula outcome, Formula coordinate) =>
        Seq(
            Call("Finite", state), Sp, Land, Sp,
            Call("Fintype", index), Sp, Land, Sp,
            Open, Forall, Sp, coordinate, Colon, Sp, index, Comma, Sp,
            Call("Fintype", new Formula.Subscript(outcome, coordinate)), Close);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Card(Formula value) =>
        Call("card", value);

    private static Formula Capacity(Formula outcome) =>
        Call("Cap", outcome);

    private static Formula Cost(Formula outcome) =>
        Call("Cost", outcome);

    private static Formula LogCardinality(Formula state) =>
        Call("logb", D(2), Card(state));
}
