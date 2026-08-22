using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class UniversalSufficiencyFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal sufficiency is equivalently target factorization or constancy on fibers.",
        H("Universal Sufficiency Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-target-factor-agrees-on-represented-coordinates"),
                DeclarationHandle.Create(DeclarationPrefix + "targetFactor_apply"),
                H("The target factor agrees on represented coordinates"),
                StatementSource.FromAuthor(TargetFactorApplyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the target is constant whenever two states have the same "
                            + "concept coordinate. The resulting map from concept coordinates "
                            + "to the target image sends every represented coordinate q_C(x) "
                            + "to the canonical target point determined by x.")),
                    Paragraph(Text(
                        "Coordinates outside the range of q_C are filled using an arbitrary "
                            + "state, which exists because the state space is nonempty. This "
                            + "choice cannot affect the represented coordinates covered by "
                            + "the lemma."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("universal-sufficiency-factorization"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "universal_sufficiency_factorization"),
                H("Universal sufficiency has three equivalent forms"),
                StatementSource.FromAuthor(UniversalSufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concept readout is sufficient for a target exactly when the "
                            + "canonical target-image readout factors through it. The same "
                            + "factorization exists exactly when the target is constant on "
                            + "each fiber of the concept readout.")),
                    Paragraph(Text(
                        "Fiber constancy makes the factor map well-defined on represented "
                            + "coordinates. Nonemptiness of the state space supplies a target "
                            + "image value for any concept coordinates that no state represents; "
                            + "the auxiliary lemma proves agreement on all represented ones.")),
                    Paragraph(Text(
                        "The repository proof reuses the pinned library's factor-through "
                            + "criterion and extension operation. Repository searches found "
                            + "adjacent factorization results but no existing declaration that "
                            + "combines this canonical target-image refinement with the fiber "
                            + "criterion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Subscript(Formula value, Formula subscript) =>
        Seq(value, Underscore, Grp(subscript));

    private static Formula FiberConstancy(
        Formula state, Formula concept, Formula target, Formula x, Formula y) =>
        Seq(
            Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Apply(concept, x), Sp, Eq, Sp, Apply(concept, y), Sp,
            Rightarrow, Sp, Apply(target, x), Sp, Eq, Sp, Apply(target, y));

    private static Formula TargetFactorApplyFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula concept = Subscript(F.Id("q"), F.Id("C"));
        Formula target = F.Id("T");
        Formula hypothesis = F.Id("h");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula factor = Apply(F.Id("targetFactor"), concept, target, hypothesis);
        Formula canonical = Apply(F.Id("canonicalTargetReadout"), target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType), type),
            Comma, RowBreak, Grp(),
            Apply(F.Id("Nonempty"), state), Comma, Sp,
            Typed(concept, Seq(state, Sp, To, Sp, conceptType)), Comma, Sp,
            Typed(target, Seq(state, Sp, To, Sp, targetType)), Comma, RowBreak, Grp(),
            Typed(
                hypothesis,
                FiberConstancy(state, concept, target, x, y)),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(x, state), Comma, Sp,
            Apply(factor, Apply(concept, x)), Sp, Eq, Sp, Apply(canonical, x), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula UniversalSufficiencyFormula()
    {
        Formula state = F.Id("X");
        Formula conceptType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula concept = Subscript(F.Id("q"), F.Id("C"));
        Formula target = F.Id("T");
        Formula factor = F.Id("f");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula canonical = Apply(F.Id("canonicalTargetReadout"), target);
        Formula targetImage = Apply(F.Id("TargetImage"), target);
        Formula factorization = Seq(
            Exists, Sp,
            Typed(factor, Seq(conceptType, Sp, To, Sp, targetImage)), Comma, Sp,
            canonical, Sp, Eq, Sp, factor, Sp, Circ, Sp, concept);
        Formula refinement = Apply(F.Id("Refines"), canonical, concept);
        Formula fiberConstancy = FiberConstancy(state, concept, target, x, y);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, conceptType, Comma, Sp, targetType), type),
            Comma, RowBreak, Grp(),
            Apply(F.Id("Nonempty"), state), Comma, Sp,
            Typed(concept, Seq(state, Sp, To, Sp, conceptType)), Comma, Sp,
            Typed(target, Seq(state, Sp, To, Sp, targetType)), Comma, RowBreak, Grp(),
            Open, refinement, Sp, Leftrightarrow, Sp, factorization, Close,
            Sp, Land, RowBreak, Grp(),
            Open, factorization, Sp, Leftrightarrow, Sp, fiberConstancy, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
