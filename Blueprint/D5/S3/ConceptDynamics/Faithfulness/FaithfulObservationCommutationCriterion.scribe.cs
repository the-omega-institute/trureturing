using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class FaithfulObservationCommutationCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/FaithfulObservationCommutationCriterion."
            + "faithful_observation_commutation_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Jointly faithful observations detect equality of two process orders.",
        H("Faithful Observation Commutation Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("faithful-observation-commutation-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Faithful observations detect commutation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The dependent family is assembled with the canonical jointReadout. "
                        + "Coordinatewise agreement of the two composite states therefore "
                        + "becomes equality of their joint readings.")),
                Paragraph(Text(
                    "Injectivity identifies those states for every input, and function "
                        + "extensionality identifies the composite processes."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula output = F.Id("Output");
        Formula readout = F.Id("Q");
        Formula first = F.Id("Fu");
        Formula second = F.Id("Fv");
        Formula index = F.Id("i");
        Formula state = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula Read(Formula i, Formula x) => Call("Q", i, x);
        Formula Apply(Formula function, Formula x) => Call("apply", function, x);
        Formula leftState = Apply(first, Apply(second, state));
        Formula rightState = Apply(second, Apply(first, state));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, indexType, Sp, To, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
                stateType, Sp, To, Sp, Call("Output", index), Comma),
            Seq(
                first, Comma, Sp, second, Colon, Sp,
                stateType, Sp, To, Sp, stateType, Comma),
            Seq(
                Call("Injective", Call("jointReadout", readout)), Sp, Land, Sp),
            Seq(
                Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
                state, Colon, Sp, stateType, Comma, Sp,
                Equal(Read(index, leftState), Read(index, rightState)), Close, Sp,
                Implies),
            Seq(
                Equal(
                    Seq(first, Sp, Circ, Sp, second),
                    Seq(second, Sp, Circ, Sp, first)), Dot),
        ]));
    }
}
