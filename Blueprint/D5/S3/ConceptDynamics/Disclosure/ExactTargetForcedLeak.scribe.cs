using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class ExactTargetForcedLeakDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact target realization exposes its sensitive common part through the leak of the "
            + "augmented public concept, and a no-new-leak hypothesis makes that exposure "
            + "already present before augmentation.",
        H("Exact Target Forced Leak"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-target-realization-forces-sensitive-disclosure"),
                DeclarationHandle.Create(DeclarationPrefix + "exact_target_forced_leak"),
                H("Exact target realization forces sensitive disclosure"),
                StatementSource.FromAuthor(ExactTargetForcedLeakFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target factors through the join of the public and added readouts. "
                            + "Because the forced part is the target's common part with the "
                            + "sensitive readout, transitivity also makes it factor through that "
                            + "augmented public join.")),
                    Paragraph(Text(
                        "The forced part already factors through the sensitive readout. These "
                            + "two lower-bound factorizations invoke the universal property of "
                            + "the augmented join's meet with the sensitive readout, forcing the "
                            + "part to factor through the resulting leak."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("structural-no-new-leak-makes-forced-leak-preexist"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "forced_leak_preexists_of_structurally_no_new_leak"),
                H("Structural no-new-leak makes the forced leak preexist"),
                StatementSource.FromAuthor(ForcedLeakPreexistsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The main theorem first places the target-forced sensitive part below the "
                        + "post-augmentation common part. Structural no-new-leak identifies that "
                        + "post-augmentation part with the prior public-sensitive common part in "
                        + "both refinement directions. Composing the relevant direction shows "
                        + "that the forced part was already disclosed by the public readout."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("boolean-coordinates-give-a-nontrivial-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "exact_target_forced_leak_nontrivial_witness"),
                H("Boolean coordinates give a nontrivial witness"),
                StatementSource.FromAuthor(NontrivialWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On pairs of Booleans, take the public readout to be the first coordinate and "
                        + "the added, sensitive, target, forced-part, and leak readouts to be the "
                        + "second coordinate. The product join realizes the target, and the second "
                        + "coordinate satisfies both meet conditions. The states (false, false) "
                        + "and (false, true) receive different forced-part values, so the instance "
                        + "carries genuine disclosure rather than a constant readout."))),
                DescribeRole.Lemma))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Meet(Formula left, Formula right, Formula meet) =>
        Call("IsConceptMeet", left, right, meet);

    private static Formula NoNewLeak(
        Formula publicConcept,
        Formula added,
        Formula sensitive,
        Formula before,
        Formula after) =>
        Call("StructurallyNoNewLeak", publicConcept, added, sensitive, before, after);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula ExactTargetForcedLeakFormula()
    {
        Formula stateType = F.Id("X");
        Formula publicType = F.Id("P");
        Formula addedType = F.Id("M");
        Formula sensitiveType = F.Id("S");
        Formula targetType = F.Id("E");
        Formula forcedType = F.Id("K");
        Formula leakType = F.Id("L");
        Formula publicConcept = F.Id("p");
        Formula added = F.Id("m");
        Formula sensitive = F.Id("s");
        Formula target = F.Id("e");
        Formula forcedPart = F.Id("k");
        Formula leak = F.Id("l");
        Formula augmented = Join(publicConcept, added);
        Formula hypotheses = And(
            Refines(target, augmented),
            And(
                Meet(target, sensitive, forcedPart),
                Meet(augmented, sensitive, leak)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("P", TypeUniverse()),
                Bound("M", TypeUniverse()),
                Bound("S", TypeUniverse()),
                Bound("E", TypeUniverse()),
                Bound("K", TypeUniverse()),
                Bound("L", TypeUniverse()),
                Bound("p", Arrow(stateType, publicType)),
                Bound("m", Arrow(stateType, addedType)),
                Bound("s", Arrow(stateType, sensitiveType)),
                Bound("e", Arrow(stateType, targetType)),
                Bound("k", Arrow(stateType, forcedType)),
                Bound("l", Arrow(stateType, leakType)),
            ],
            ImpliesFormula(hypotheses, Refines(forcedPart, leak))));
    }

    private static Formula ForcedLeakPreexistsFormula()
    {
        Formula stateType = F.Id("X");
        Formula publicType = F.Id("P");
        Formula addedType = F.Id("M");
        Formula sensitiveType = F.Id("S");
        Formula targetType = F.Id("E");
        Formula forcedType = F.Id("K");
        Formula beforeType = F.Id("Before");
        Formula afterType = F.Id("After");
        Formula publicConcept = F.Id("p");
        Formula added = F.Id("m");
        Formula sensitive = F.Id("s");
        Formula target = F.Id("e");
        Formula forcedPart = F.Id("k");
        Formula before = F.Id("before");
        Formula after = F.Id("after");
        Formula augmented = Join(publicConcept, added);
        Formula hypotheses = And(
            Refines(target, augmented),
            And(
                Meet(target, sensitive, forcedPart),
                NoNewLeak(publicConcept, added, sensitive, before, after)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("P", TypeUniverse()),
                Bound("M", TypeUniverse()),
                Bound("S", TypeUniverse()),
                Bound("E", TypeUniverse()),
                Bound("K", TypeUniverse()),
                Bound("Before", TypeUniverse()),
                Bound("After", TypeUniverse()),
                Bound("p", Arrow(stateType, publicType)),
                Bound("m", Arrow(stateType, addedType)),
                Bound("s", Arrow(stateType, sensitiveType)),
                Bound("e", Arrow(stateType, targetType)),
                Bound("k", Arrow(stateType, forcedType)),
                Bound("before", Arrow(stateType, beforeType)),
                Bound("after", Arrow(stateType, afterType)),
            ],
            ImpliesFormula(hypotheses, Refines(forcedPart, before))));
    }

    private static Formula NontrivialWitnessFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula pair = Seq(boolean, Sp, Times, Sp, boolean);
        Formula first = F.Id("fst");
        Formula second = F.Id("snd");
        Formula input = F.Id("x");
        Formula otherInput = F.Id("y");
        Formula augmented = Join(first, second);
        Formula distinguished = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", pair), Bound("y", pair)],
            NotEqual(Apply(second, input), Apply(second, otherInput)));

        return Disp(And(
            Refines(second, augmented),
            And(
                Meet(second, second, second),
                And(
                    Meet(augmented, second, second),
                    And(Refines(second, second), distinguished)))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
