using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class FiniteWindowMinimalSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semiconjugate descents compose, and a finite orbit window is the coarsest readout "
            + "sufficient for every observation in that window.",
        H("Finite-Window Minimal Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semiconjugate-descents-compose"),
                DeclarationHandle.Create(DeclarationPrefix + "descent_composes"),
                H("Semiconjugate descents compose"),
                StatementSource.FromAuthor(DescentCompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose q carries the state update F to an update Fbar on an "
                            + "intermediate space, and r carries Fbar to an update Ftilde on "
                            + "a second space. Their composite r after q then carries F directly "
                            + "to Ftilde.")),
                    Paragraph(Text(
                        "This transitivity statement is purely structural: it requires neither "
                            + "finite spaces nor inhabited spaces, and follows by substituting "
                            + "the first intertwining equality into the second."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-window-is-minimally-sufficient"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_window_minimal_sufficiency"),
                H("The finite orbit window is minimally sufficient"),
                StatementSource.FromAuthor(FiniteWindowMinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite-window readout records q along the orbit from time zero "
                            + "through time n. For every index in that range, the canonical "
                            + "readout of the corresponding observed value factors through the "
                            + "whole window.")),
                    Paragraph(Text(
                        "Conversely, if a candidate readout p is sufficient for every one of "
                            + "those canonical observed targets, the entire finite window factors "
                            + "through p. Under the convention that Refines(coarse, fine) means "
                            + "the coarse readout factors through the fine one, this makes the "
                            + "window the coarsest simultaneously sufficient readout.")),
                    Paragraph(Text(
                        "The state space is assumed nonempty so that canonical target-image "
                            + "factorizations are available. No finiteness assumption is imposed "
                            + "on the state or observation types, and the conclusion includes the "
                            + "zero horizon n = 0."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula DescentCompositionFormula()
    {
        Formula state = F.Id("X");
        Formula intermediate = F.Id("B");
        Formula target = F.Id("C");
        Formula update = F.Id("F");
        Formula intermediateUpdate = F.Id("Fbar");
        Formula targetUpdate = F.Id("Ftilde");
        Formula firstDescent = F.Id("q");
        Formula secondDescent = F.Id("r");
        Formula stateValue = F.Id("x");
        Formula intermediateValue = F.Id("b");
        Formula firstIntertwining = Seq(
            Forall, Sp, Typed(stateValue, state), Comma, Sp,
            Equal(
                Apply(firstDescent, Apply(update, stateValue)),
                Apply(intermediateUpdate, Apply(firstDescent, stateValue))));
        Formula secondIntertwining = Seq(
            Forall, Sp, Typed(intermediateValue, intermediate), Comma, Sp,
            Equal(
                Apply(secondDescent, Apply(intermediateUpdate, intermediateValue)),
                Apply(targetUpdate, Apply(secondDescent, intermediateValue))));
        Formula compositeIntertwining = Seq(
            Forall, Sp, Typed(stateValue, state), Comma, Sp,
            Equal(
                Apply(secondDescent, Apply(firstDescent, Apply(update, stateValue))),
                Apply(targetUpdate, Apply(secondDescent, Apply(firstDescent, stateValue)))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, intermediate, Comma, Sp, target), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(intermediateUpdate, Arrow(intermediate, intermediate)), Comma, Sp,
            Typed(targetUpdate, Arrow(target, target)), Comma, RowBreak, Grp(),
            Typed(firstDescent, Arrow(state, intermediate)), Comma, Sp,
            Typed(secondDescent, Arrow(intermediate, target)), Comma, RowBreak, Grp(),
            Open, firstIntertwining, Close, Sp, Land, Sp,
            Open, secondIntertwining, Close, Sp, Rightarrow, RowBreak, Grp(),
            compositeIntertwining, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteWindowMinimalityFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula candidateType = F.Id("C");
        Formula observation = F.Id("q");
        Formula update = F.Id("F");
        Formula horizon = F.Id("n");
        Formula index = F.Id("i");
        Formula candidate = F.Id("p");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula indexType = Call("Fin", Add(horizon, D(1)));
        Formula orbitTarget = Call("orbitTarget", observation, update, index);
        Formula window = Call("finiteWindow", observation, update, horizon);
        Formula canonicalOrbitTarget = Call("canonicalTargetReadout", orbitTarget);
        Formula componentSufficiency = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", canonicalOrbitTarget, window));
        Formula candidateSufficiency = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", canonicalOrbitTarget, candidate));
        Formula minimality = Seq(
            Forall, Sp, Typed(candidateType, TypeUniverse()), Comma, Sp,
            Typed(candidate, Arrow(state, candidateType)), Comma, RowBreak, Grp(),
            Open, candidateSufficiency, Close, Sp, Rightarrow, Sp,
            Call("Refines", window, candidate));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Call("Nonempty", state), Comma, Sp,
            Typed(observation, Arrow(state, observationType)), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Open, componentSufficiency, Close, Sp, Land, RowBreak, Grp(),
            Open, minimality, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
