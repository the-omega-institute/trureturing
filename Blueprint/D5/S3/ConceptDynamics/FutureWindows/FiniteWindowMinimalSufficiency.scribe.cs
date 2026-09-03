using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.FutureWindows;

internal sealed class FiniteWindowMinimalSufficiencyDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The realized finite orbit window is sufficient for every target in the window, "
            + "and every simultaneously sufficient effective-image interface determines "
            + "the entire realized window.",
        H("Finite-Window Minimal Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-finite-window-is-sufficient-and-coarsest"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_future_window_minimal_sufficiency"),
                H("The finite window is simultaneously sufficient and coarsest"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each index from zero through n, the canonical readout into "
                            + "the realized image of the corresponding orbit target factors "
                            + "through the canonical readout into the realized image of the "
                            + "whole finite window. This is target sufficiency with both "
                            + "interfaces restricted to their effective images.")),
                    Paragraph(Text(
                        "Conversely, let r be any interface whose realized image is sufficient "
                            + "for every orbit target in the window. The realized finite-window "
                            + "readout then factors through the realized image of r. With "
                            + "Refines(coarse, fine) meaning that coarse factors through fine, "
                            + "this is exactly the coarsest factor-through property.")),
                    Paragraph(Text(
                        "No inhabitedness, finiteness, or dynamical hypothesis is assumed. "
                            + "The finite dependent product includes horizon zero, and the "
                            + "effective-image clause remains valid for an empty state type."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula candidateType = F.Id("C");
        Formula observation = F.Id("q");
        Formula update = F.Id("F");
        Formula horizon = F.Id("n");
        Formula index = F.Id("i");
        Formula candidate = F.Id("r");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula indexType = Call("Fin", Add(horizon, D(1)));
        Formula target = Call("orbitTarget", observation, update, index);
        Formula window = Call("finiteWindow", observation, update, horizon);
        Formula effectiveTarget = Call("canonicalTargetReadout", target);
        Formula effectiveWindow = Call("canonicalTargetReadout", window);
        Formula simultaneousSufficiency = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", effectiveTarget, effectiveWindow));
        Formula candidateSufficiency = Seq(
            Forall, Sp, Typed(index, indexType), Comma, Sp,
            Call("Refines", effectiveTarget, Call("canonicalTargetReadout", candidate)));
        Formula coarseness = Seq(
            Forall, Sp, Typed(candidateType, TypeUniverse()), Comma, Sp,
            Typed(candidate, Arrow(state, candidateType)), Comma, RowBreak, Grp(),
            Open, candidateSufficiency, Close, Sp, Rightarrow, Sp,
            Call("Refines", effectiveWindow, Call("canonicalTargetReadout", candidate)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(observation, Arrow(state, observationType)), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Open, simultaneousSufficiency, Close, Sp, Land, RowBreak, Grp(),
            Open, coarseness, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
