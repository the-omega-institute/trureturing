using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class TailResidualCrossLayerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lipschitz update separates a coarse defect into a fine tail and cross-layer defect.",
        H("Tail Residual Cross-Layer Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tail-residual-cross-layer-defect-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/TailResidualCrossLayerBound."
                        + "tail_residual_cross_layer_defect_bound"),
                H("Tail residual cross-layer defect bound"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V_m be a visible Hilbert subspace of V_n, with canonical "
                            + "orthogonal projections P_m and P_n. Let F be L-Lipschitz.")),
                    Paragraph(Text(
                        "The coarse defect compares projecting F(X) with projecting F after "
                            + "the coarse projection. It is bounded by the Lipschitz image of "
                            + "the unresolved V_n tail plus the same defect evaluated after "
                            + "the fine projection.")),
                    Paragraph(Text(
                        "Both defect terms are expanded directly from F and the canonical "
                            + "projections. The proof inserts the fine projected update, applies "
                            + "the triangle inequality and projection contraction, then uses "
                            + "P_m P_n = P_m for nested subspaces."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Projection(Formula index, Formula value) =>
        Apply(new Formula.Subscript(F.Id("P"), index), value);

    private static Formula Defect(Formula m, Formula function, Formula value) =>
        new Formula.Norm(Seq(
            Projection(m, Apply(function, value)), Sp, Minus, Sp,
            Projection(m, Apply(function, Projection(m, value)))));

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula x = F.Id("X");
        Formula function = F.Id("F");
        Formula constant = F.Id("L");
        Formula fineProjection = Projection(n, x);
        Formula tail = new Formula.Norm(Seq(x, Sp, Minus, Sp, fineProjection));
        Formula nesting = Seq(
            new Formula.Subscript(F.Id("V"), m), Sp, Subseteq, Sp,
            new Formula.Subscript(F.Id("V"), n));
        Formula lipschitz = Seq(
            Operatorname, Grp(F.Id("Lipschitz")), Underscore, Grp(constant),
            Open, function, Close);
        Formula bound = Seq(
            Defect(m, function, x), Sp, Leq, Sp,
            constant, Sp, tail, Sp, Plus, Sp,
            Defect(m, function, fineProjection));
        return Disp(Seq(nesting, Sp, Land, Sp, lipschitz, Sp, Rightarrow, Sp, bound, Dot));
    }
}
