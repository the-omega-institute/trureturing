using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class DenseOrbitInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous observable invariant under an update with a dense forward orbit is constant.",
        H("Dense-Orbit Invariant Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-continuous-dense-orbit-invariant-is-constant"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/DenseOrbitInvariant."
                        + "continuous_invariant_of_dense_orbit_constant"),
                H("A continuous dense-orbit invariant is constant"),
                StatementSource.FromAuthor(DenseOrbitInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be an arbitrary topological space, Y a Hausdorff space, step an "
                            + "update on X, and observable a continuous map from X to Y. Assume "
                            + "the forward orbit of x0 is dense and observable is unchanged by "
                            + "every update. Then observable agrees everywhere with its value at x0.")),
                    Paragraph(Text(
                        "Update invariance first propagates by induction along every finite "
                            + "iterate of the orbit. Mathlib's Continuous.ext_on then extends "
                            + "this equality from the dense orbit to all of X; Hausdorffness of "
                            + "Y is exactly the separation hypothesis used by that theorem.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no theorem combining forward "
                            + "iteration, invariance, and a dense orbit. Smart-search queries for "
                            + "continuous invariant functions on dense orbits and equality of "
                            + "continuous functions on dense sets identified Continuous.ext_on as "
                            + "the reusable extension theorem.")),
                    Paragraph(Text(
                        "This result closes only the general dense-orbit mechanism in residual "
                            + "theorem 6.31. It does not formalize or claim the source theorem's "
                            + "full kernel-equals-center characterization."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var separated = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                separated.Add(Comma);
                separated.Add(Sp);
            }

            separated.Add(arguments[index]);
        }

        return Seq(function, Open, Seq([.. separated]), Close);
    }

    private static Formula DenseOrbitInvariantFormula()
    {
        Formula xType = F.Id("X");
        Formula yType = F.Id("Y");
        Formula x = F.Id("x");
        Formula x0 = Seq(x, Underscore, D(0));
        Formula step = F.Id("step");
        Formula observable = F.Id("observable");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula iterate = Seq(step, Caret, F.Id("n"));

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, yType, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("TopologicalSpace")),
            Open, xType, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("TopologicalSpace")),
            Open, yType, Close, CloseBracket, Sp,
            OpenBracket, Operatorname, Grp(F.Id("T2Space")),
            Open, yType, Close, CloseBracket, Comma, Esc,
            step, Colon, Sp, xType, Sp, To, Sp, xType, Comma, Sp,
            observable, Colon, Sp, xType, Sp, To, Sp, yType, Comma, Sp,
            x0, Colon, Sp, xType, Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("Continuous"))), observable), Sp, Land, Sp,
            Apply(Seq(Operatorname, Grp(F.Id("DenseRange"))),
                Seq(Open, F.Id("n"), InMacro, Sp, naturals, Sp, Mapsto, Sp,
                    Apply(iterate, x0), Close)), Sp, Land, Esc,
            Open, Forall, Sp, x, Comma, Sp,
            Apply(observable, Apply(step, x)), Sp, Eq, Sp,
            Apply(observable, x), Close, Sp, Rightarrow, Esc,
            Forall, Sp, x, Comma, Sp,
            Apply(observable, x), Sp, Eq, Sp, Apply(observable, x0), Dot));
    }
}
