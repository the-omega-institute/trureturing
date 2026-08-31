using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class ModelRelativeCompletenessDifferenceCriterionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Faithfulness/"
            + "ModelRelativeCompletenessDifferenceCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completeness relative to a prior model is equivalent to the observer residual "
            + "meeting the model difference set only at zero.",
        H("Model-Relative Completeness and the Difference Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("model-relative-completeness-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "modelRelativeComplete"),
                H("Model-relative completeness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A readout family is complete on a model when its joint readout is "
                        + "injective after the state type is restricted to that model."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("model-difference-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "modelDifference"),
                H("The model difference set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The difference set consists of every ordered difference x - y of "
                        + "two states belonging to the prior model."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-difference-residual-definition"),
                DeclarationHandle.Create(DeclarationPrefix + "jointDifferenceResidual"),
                H("The additive joint residual"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A difference belongs to the additive residual when the imported "
                        + "joint kernel cannot distinguish it from zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("model-relative-completeness-difference-criterion"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "model_relative_completeness_difference_criterion"),
                H("Completeness is the zero-intersection criterion"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Additivity turns equality of all readings at x and y into "
                            + "membership of x - y in the additive joint residual.")),
                    Paragraph(Text(
                        "Thus a collision inside the model gives a nonzero point of the "
                            + "intersection, and every nonzero point of the intersection "
                            + "reconstructs a collision in the restricted joint readout.")),
                    Paragraph(Text(
                        "The reverse implication reuses the frozen local-global residual "
                            + "criterion on the subtype of model states. Nonemptiness is "
                            + "used only to put zero into the model difference set. This "
                            + "closes atom generic-residual-3f7117a0063a50720284293a156821"
                            + "caec1fd36507f73246da479e340fd396b5."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("model-nonempty-premise-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "model_nonempty_is_necessary"),
                H("The nonempty-model premise is necessary"),
                StatementSource.FromAuthor(NonemptyNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the empty subset of the integers, restricted completeness is "
                        + "vacuous. Its difference set is empty, so the intersection cannot "
                        + "equal the singleton zero set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("additivity-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "additivity_is_necessary"),
                H("Additivity is necessary"),
                StatementSource.FromAuthor(AdditivityNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integer squaring readout identifies -1 and 1 on the two-state "
                        + "model. Its zero residual contains only zero, while the model "
                        + "differences are zero and the two signed differences. Hence the "
                        + "intersection criterion holds although completeness fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("additive-carrier-is-nonempty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "additive_carrier_is_nonempty"),
                H("An additive carrier is nonempty"),
                StatementSource.FromAuthor(AdditiveCarrierFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero element witnesses that an additive carrier cannot be empty."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unit-model-is-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "unit_model_is_complete"),
                H("The unit model is complete"),
                StatementSource.FromAuthor(UnitModelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any readout is injective after restriction to a one-element state type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-coordinate-singleton-model-is-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_coordinate_singleton_model_is_complete"),
                H("No coordinates suffice on a singleton model"),
                StatementSource.FromAuthor(EmptyCoordinateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty readout family is complete when the prior model is the "
                        + "singleton integer zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-readout-is-incomplete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_readout_is_incomplete"),
                H("A constant readout is incomplete"),
                StatementSource.FromAuthor(ConstantReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant readout cannot separate false from true in the full "
                        + "Boolean model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-readout-is-complete-on-every-model"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identity_readout_is_complete_on_every_model"),
                H("Identity is complete on every model"),
                StatementSource.FromAuthor(IdentityReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An identity coordinate remains injective after restriction to any "
                        + "prior model."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula readout = F.Id("q");
        Formula model = F.Id("M");
        Formula residual = Call("jointDifferenceResidual", readout);
        Formula differences = Call("modelDifference", model);

        return Disp(Seq(
            Call("modelRelativeComplete", readout, model), Sp, Iff, Sp,
            Call("Intersection", residual, differences), Sp, Eq, Sp,
            OpenBrace, D(0), CloseBrace, Dot));
    }

    private static Formula NonemptyNecessityFormula()
    {
        Formula identity = F.Id("id");
        Formula complete = Call("modelRelativeComplete", identity, Emptyset);
        Formula intersection = Call(
            "Intersection",
            Call("jointDifferenceResidual", identity),
            Call("modelDifference", Emptyset));

        return Disp(Seq(
            complete, Sp, Land, Sp,
            NotEqual(intersection, Seq(OpenBrace, D(0), CloseBrace)), Dot));
    }

    private static Formula AdditivityNecessityFormula()
    {
        Formula square = F.Id("square");
        Formula model = Seq(
            OpenBrace, Minus, D(1), Comma, Sp, D(1), CloseBrace);
        Formula complete = Call("modelRelativeComplete", square, model);
        Formula intersection = Call(
            "Intersection",
            Call("jointDifferenceResidual", square),
            Call("modelDifference", model));

        return Disp(Seq(
            Neg, complete, Sp, Land, Sp,
            Equal(intersection, Seq(OpenBrace, D(0), CloseBrace)), Dot));
    }

    private static Formula AdditiveCarrierFormula()
    {
        Formula carrier = F.Id("X");

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp,
            Call("AddGroup", carrier), Sp, Implies, Sp,
            Call("Nonempty", carrier), Dot));
    }

    private static Formula UnitModelFormula() =>
        Disp(Seq(
            Call("modelRelativeComplete", F.Id("unitReadout"), F.Id("univ")),
            Dot));

    private static Formula EmptyCoordinateFormula() =>
        Disp(Seq(
            Call(
                "modelRelativeComplete",
                F.Id("emptyReadoutFamily"),
                Seq(OpenBrace, D(0), CloseBrace)),
            Dot));

    private static Formula ConstantReadoutFormula() =>
        Disp(Seq(
            Neg,
            Call("modelRelativeComplete", F.Id("constant"), F.Id("Bool")),
            Dot));

    private static Formula IdentityReadoutFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("M"), Comma, Sp,
            Call("modelRelativeComplete", F.Id("id"), F.Id("M")),
            Dot));
}
