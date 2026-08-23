using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class TargetRelativeBiinterpretationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mutual recovery of selected targets transports answerability without identifying all internal states.",
        H("Target-Relative Biinterpretation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-relative-biinterpretation-transports-answerability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/TargetRelativeBiinterpretation."
                        + "target_relative_biinterpretation_transports_answerability"),
                H("Target-relative recovery transports answerability without state isomorphism"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forward translation h, reverse translation k, and both indexed target "
                            + "families are public source primitives. If every source target is "
                            + "recovered after h then k, that target factors through h using its "
                            + "composition with k as the answer map.")),
                    Paragraph(Text(
                        "The reverse argument has a disjoint recovery premise: if every target-model "
                            + "target is recovered after k then h, it factors through k using its "
                            + "composition with h. These are the two public Refines conclusions from "
                            + "the family's canonical answerability relation.")),
                    Paragraph(Text(
                        "The public countermodel uses internal states Bool times Bool. The forward "
                            + "map replaces the second coordinate by false, the reverse map replaces "
                            + "it by true, and both target families observe only the first coordinate. "
                            + "Both target-recovery equations therefore hold.")),
                    Paragraph(Text(
                        "Each translation identifies states that differ only in the second coordinate, "
                            + "so neither is bijective. Their composites set that coordinate to true "
                            + "or false and hence neither composite is the identity. Thus agreement on "
                            + "all selected targets does not imply isomorphism of internal states.")),
                    Paragraph(Text(
                        "The module imports Concept and Refines as the family single source of truth. "
                            + "The concrete maps are coordinate constructions, not definitions of the "
                            + "factorization or non-isomorphism conclusions."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/ConceptJoinUniversal"))]));

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Concept(Formula domain, Formula codomain) =>
        Call("Concept", domain, codomain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula UniversalTransportFormula()
    {
        Formula type = F.Id("Type");
        Formula source = F.Id("X");
        Formula target = F.Id("Y");
        Formula sourceIndex = F.Id("I");
        Formula targetIndex = F.Id("J");
        Formula sourceValue = F.Id("A");
        Formula targetValue = F.Id("B");
        Formula forward = F.Id("h");
        Formula reverse = F.Id("k");
        Formula sourceTargets = F.Id("T");
        Formula targetTargets = F.Id("S");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula sourceTarget = new Formula.Subscript(sourceTargets, i);
        Formula targetTarget = new Formula.Subscript(targetTargets, j);
        Formula sourceRecovery = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            sourceIndex,
            Equal(Compose(Compose(sourceTarget, reverse), forward), sourceTarget));
        Formula targetRecovery = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"),
            targetIndex,
            Equal(Compose(Compose(targetTarget, forward), reverse), targetTarget));
        Formula sourceAnswerability = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            sourceIndex,
            Call("Refines", sourceTarget, forward));
        Formula targetAnswerability = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"),
            targetIndex,
            Call("Refines", targetTarget, reverse));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("Y", type),
                Bound("I", type),
                Bound("J", type),
                Bound("A", type),
                Bound("B", type),
                Bound("h", Arrow(source, target)),
                Bound("k", Arrow(target, source)),
                Bound("T", Arrow(sourceIndex, Concept(source, sourceValue))),
                Bound("S", Arrow(targetIndex, Concept(target, targetValue))),
            ],
            And(
                ImpliesFormula(sourceRecovery, sourceAnswerability),
                ImpliesFormula(targetRecovery, targetAnswerability)));
    }

    private static Formula CountermodelFormula()
    {
        Formula forward = F.Id("eraseSecondCoordinate");
        Formula reverse = F.Id("setSecondTrueCoordinate");
        Formula visible = F.Id("firstCoordinateTarget");
        Formula identity = F.Id("id");

        return And(
            Equal(Compose(Compose(visible, reverse), forward), visible),
            And(
                Equal(Compose(Compose(visible, forward), reverse), visible),
                And(
                    new Formula.Not(Call("Bijective", forward)),
                    And(
                        new Formula.Not(Call("Bijective", reverse)),
                        And(
                            NotEqual(Compose(reverse, forward), identity),
                            NotEqual(Compose(forward, reverse), identity))))));
    }

    private static Formula TheoremFormula() =>
        Disp(Seq(
            Open, UniversalTransportFormula(), Close,
            Sp, Land, Sp,
            Open, CountermodelFormula(), Close));
}
