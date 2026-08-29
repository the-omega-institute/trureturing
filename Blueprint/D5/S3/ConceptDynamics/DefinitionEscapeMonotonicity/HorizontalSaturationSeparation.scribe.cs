using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity;

internal sealed class HorizontalSaturationSeparationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/"
            + "HorizontalSaturationSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A larger sensor budget can repair one family, while a saturated language may fail.",
        H("Horizontal Saturation Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("interface-family"),
                DeclarationHandle.Create(DeclarationPrefix + "InterfaceFamily"),
                H("Typed interface family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An InterfaceFamily assigns a possibly dependent observation type and "
                        + "readout to each sensor index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("interface-union"),
                DeclarationHandle.Create(DeclarationPrefix + "interfaceUnion"),
                H("Union of all interfaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full union is the canonical dependent jointReadout of every sensor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("subfamily-union"),
                DeclarationHandle.Create(DeclarationPrefix + "subfamilyUnion"),
                H("Union of a selected subfamily"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A selected subset is represented by its subtype and joined with the same "
                        + "canonical jointReadout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("budget-insufficient"),
                DeclarationHandle.Create(DeclarationPrefix + "BudgetInsufficient"),
                H("Repairable budget insufficiency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The current subfamily is inadequate, but a strict expansion drawn from "
                        + "the already available sensor family is adequate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observation-language-insufficient"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "ObservationLanguageInsufficient"),
                H("Saturated observation-language insufficiency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The observation language is insufficient when its full interface union "
                        + "cannot recover the target."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("semantic-completion"),
                DeclarationHandle.Create(DeclarationPrefix + "semanticCompletion"),
                H("Completion by a new semantic coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Semantic completion joins the saturated old profile with the target as a "
                        + "new coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("semantic-completion-preserves-and-recovers"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "semantic_completion_preserves_family_and_recovers_target"),
                H("Semantic completion preserves the family and recovers the target"),
                StatementSource.FromAuthor(PreservationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The canonical concept join projects to the entire old sensor profile and "
                        + "to the newly added target coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("semantic-completion-minimal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "semantic_completion_minimal"),
                H("Semantic completion is the least common refinement"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every candidate exposing both the old interface union and the target also "
                        + "exposes their semantic completion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-sensor-family"),
                DeclarationHandle.Create(DeclarationPrefix + "budgetSensorFamily"),
                H("Budget-insufficiency sensor witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean witness family contains a constant sensor and an identity "
                        + "sensor with the same output type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("constant-sensor-family"),
                DeclarationHandle.Create(DeclarationPrefix + "constantSensorFamily"),
                H("Observation-language witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The language-insufficiency witness has one constant sensor on Boolean "
                        + "states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("family-visibility-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "family_visibility_is_necessary"),
                H("Semantic minimality needs visibility of the old family"),
                StatementSource.FromAuthor(FamilyVisibilityNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant candidate recovers a constant target, but it cannot recover "
                        + "the completion of the Boolean budget family. Thus family visibility "
                        + "cannot be dropped from semantic minimality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-visibility-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "target_visibility_is_necessary"),
                H("Semantic minimality needs visibility of the target"),
                StatementSource.FromAuthor(TargetVisibilityNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full constant family recovers itself, but it cannot recover a "
                        + "completion carrying the Boolean target. Thus target visibility "
                        + "cannot be dropped from semantic minimality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-insufficiency-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "budget_insufficiency_witness"),
                H("Adding an available sensor repairs a deficient budget"),
                StatementSource.FromAuthor(BudgetWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected constant sensor cannot recover Boolean identity. Strictly "
                        + "expanding to the full family adds the existing identity sensor and "
                        + "provides an exact decoder."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("observation-language-insufficiency-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "observation_language_insufficiency_witness"),
                H("No subfamily or repeated transcript repairs a constant language"),
                StatementSource.FromAuthor(LanguageWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The full constant family is inadequate, so the imported subfamily "
                            + "persistence theorem rules out every selected subset.")),
                    Paragraph(Text(
                        "Its transcript kernel factors through the same full union after every "
                            + "iid repetition, including zero samples. The imported kernel "
                            + "barrier therefore keeps the Boolean target unidentified."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget-does-not-imply-language-insufficiency"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "budget_insufficiency_does_not_imply_"
                        + "observation_language_insufficiency"),
                H("Budget insufficiency does not imply language insufficiency"),
                StatementSource.FromAuthor(NonimplicationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named budget witness is repairable by an existing sensor, and its full "
                        + "family already recovers the target. It therefore witnesses the formal "
                        + "nonimplication between the two notions."))),
                DescribeRole.Theorem))));

    private static Formula Adequate(Formula readout, Formula target) =>
        Call("TargetAdequate", readout, target);

    private static Formula FullUnion(Formula family) =>
        Call("interfaceUnion", family);

    private static Formula SubUnion(Formula family, Formula selected) =>
        Call("subfamilyUnion", family, selected);

    private static Formula Budget(Formula family, Formula target, Formula selected) =>
        Call("BudgetInsufficient", family, target, selected);

    private static Formula Language(Formula family, Formula target) =>
        Call("ObservationLanguageInsufficient", family, target);

    private static Formula Completion(Formula family, Formula target) =>
        Call("semanticCompletion", family, target);

    private static Formula PreservationFormula()
    {
        Formula family = F.Id("q");
        Formula target = F.Id("T");
        Formula completion = Completion(family, target);

        return Disp(Seq(
            Forall, Sp, family, Comma, Sp, target, Comma, Sp,
            Call("Refines", FullUnion(family), completion), Sp, Land, Sp,
            Adequate(completion, target), Dot));
    }

    private static Formula MinimalityFormula()
    {
        Formula family = F.Id("q");
        Formula target = F.Id("T");
        Formula candidate = F.Id("C");
        Formula visibleFamily = Call("Refines", FullUnion(family), candidate);
        Formula visibleTarget = Adequate(candidate, target);

        return Disp(Seq(
            Forall, Sp, family, Comma, Sp, target, Comma, Sp, candidate, Comma, Sp,
            visibleFamily, Sp, Land, Sp, visibleTarget, Sp, Rightarrow, Sp,
            Call("Refines", Completion(family, target), candidate), Dot));
    }

    private static Formula BudgetWitnessFormula()
    {
        Formula family = F.Id("budgetSensorFamily");
        Formula target = F.Id("booleanTarget");
        Formula selected = Seq(OpenBrace, F.Id("false"), CloseBrace);

        return Disp(Seq(Budget(family, target, selected), Dot));
    }

    private static Formula FamilyVisibilityNecessityFormula()
    {
        Formula family = F.Id("budgetSensorFamily");
        Formula constant = F.Id("constUnit");

        return Disp(Seq(
            Adequate(constant, constant), Sp, Land, Sp, Neg, Sp,
            Call("Refines", Completion(family, constant), constant), Dot));
    }

    private static Formula TargetVisibilityNecessityFormula()
    {
        Formula family = F.Id("constantSensorFamily");
        Formula fullUnion = FullUnion(family);
        Formula target = F.Id("booleanTarget");

        return Disp(Seq(
            Call("Refines", fullUnion, fullUnion), Sp, Land, Sp, Neg, Sp,
            Call("Refines", Completion(family, target), fullUnion), Dot));
    }

    private static Formula LanguageWitnessFormula()
    {
        Formula family = F.Id("constantSensorFamily");
        Formula target = F.Id("booleanTarget");
        Formula selected = F.Id("J");
        Formula sampleCount = F.Id("n");
        Formula kernel = F.Id("constantBooleanTranscriptKernel");
        Formula repeated = Call("iidRepetition", sampleCount, kernel);

        return Disp(new Formula.Aligned([
            Seq(Language(family, target), Sp, Land),
            Seq(
                Open, Forall, Sp, selected, Subseteq, Sp, F.Id("Unit"), Comma, Sp,
                Neg, Sp, Adequate(SubUnion(family, selected), target), Close, Sp, Land),
            Seq(
                Forall, Sp, sampleCount, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                Call("KernelFactorsThrough", FullUnion(family), repeated), Sp, Land),
            Seq(Neg, Sp, Call("IdentifiesTarget", repeated, target), Dot),
        ]));
    }

    private static Formula NonimplicationFormula()
    {
        Formula family = F.Id("budgetSensorFamily");
        Formula target = F.Id("booleanTarget");
        Formula selected = Seq(OpenBrace, F.Id("false"), CloseBrace);

        return Disp(Seq(
            Neg, Sp, Open, Budget(family, target, selected), Sp, Rightarrow, Sp,
            Language(family, target), Close, Dot));
    }
}
