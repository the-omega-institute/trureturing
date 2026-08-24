using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class FiniteWindowStabilityIsDescentDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Dialectics/FiniteWindowStabilityIsDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite observation window is stable exactly when its update preserves fibers "
            + "and descends uniquely to the realized window image.",
        H("Finite-Window Stability Is Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("depth-one-window-is-the-next-window"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "depth_one_finite_window_eq_next_window"),
                H("The depth-one window kernel is the next window kernel"),
                StatementSource.FromAuthor(DepthOneWindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The depth-n window records the observations at times zero through n. "
                            + "Its depth-one kernel requires equality both on that current "
                            + "window and on the same window after one update.")),
                    Paragraph(Text(
                        "The two overlapping windows therefore require equality exactly at "
                            + "times zero through n + 1. Their depth-one kernel is the "
                            + "finite-window kernel at the next horizon, for arbitrary state "
                            + "and observation types."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-window-stability-is-descent"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_window_stability_congruence_descent_tfae"),
                H("Finite-window stability is equivalent to congruence and descent"),
                StatementSource.FromAuthor(StabilityDescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Stability at horizon n says that equality of observations through "
                            + "time n already determines equality through time n + 1. This is "
                            + "equivalent to the update preserving every fiber of the "
                            + "depth-n window readout.")),
                    Paragraph(Text(
                        "The same condition is equivalent to a unique descended update on the "
                            + "realized image of that window, commuting with the original state "
                            + "update. Thus kernel stability, interface congruence, and effective "
                            + "descent are three forms of one condition.")),
                    Paragraph(Text(
                        "The equivalence holds without finiteness or nonemptiness assumptions "
                            + "on the state and observation types, including the zero horizon."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula DepthOneWindowFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula observation = F.Id("q");
        Formula update = F.Id("F");
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula window = Call("finiteWindow", observation, update, horizon);
        Formula nextHorizon = Add(horizon, D(1));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(observation, Arrow(state, observationType)), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Call("depthOneKernel", window, update), Sp, Eq, Sp,
            Call("finiteWindowKernel", observation, update, nextHorizon), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula StabilityDescentFormula()
    {
        Formula state = F.Id("X");
        Formula observationType = F.Id("O");
        Formula observation = F.Id("q");
        Formula update = F.Id("F");
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula nextHorizon = Add(horizon, D(1));
        Formula window = Call("finiteWindow", observation, update, horizon);
        Formula currentKernel =
            Call("finiteWindowKernel", observation, update, horizon);
        Formula nextKernel =
            Call("finiteWindowKernel", observation, update, nextHorizon);
        Formula conditions = Grp(
            OpenBracket,
            Seq(currentKernel, Sp, Eq, Sp, nextKernel), Comma, Sp,
            Call("InterfaceCongruence", window, update), Comma, Sp,
            Call("EffectiveDescent", window, update),
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, observationType), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Typed(observation, Arrow(state, observationType)), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Call("ListTFAE", conditions), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
