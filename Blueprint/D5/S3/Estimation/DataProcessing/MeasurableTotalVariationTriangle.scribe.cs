using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class MeasurableTotalVariationTriangleDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Truncated-difference suprema give measurable total variation its triangle and "
            + "symmetry laws.",
        H("Measurable Total Variation Triangle"),
        Blocks(
            Paragraph(Text(
                "The quantity measurableTotalVariation mu nu is the supremum over measurable "
                    + "events of the larger of the two truncated differences of the measures "
                    + "on that event. It lives in the frozen module "
                    + "MeasurablePostprocessingDefectContraction, imported here. The formulas "
                    + "below abbreviate this quantity as mTV.")),
            Paragraph(Text(
                "The general lemma carries the whole argument. iSup_max_tsub_triangle mentions "
                    + "no measure and no measurable structure: it is the order theory of "
                    + "truncated subtraction over an arbitrary index. The measure statement is "
                    + "its event-indexed instance, proved in one line.")),
            Paragraph(Text(
                "An earlier draft stated only the measure version and argued in its own prose "
                    + "that the general form could not be given without introducing a second "
                    + "definition of the quantity. A review seat showed that argument was "
                    + "wrong: the general lemma can be stated inline over Index -> ENNReal, "
                    + "redefining nothing. It is now the primary theorem.")),
            Paragraph(Text(
                "The demand for the triangle law comes from two frozen modules, "
                    + "Estimation/DataProcessing/MeasurableDescentErrorBounds and "
                    + "Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle. Each "
                    + "privately proves the same unrestricted proposition: the same statement, "
                    + "proved twice. Their strategies are near-identical, but they are not "
                    + "literally the same proof text.")),
            Paragraph(Text(
                "Both modules are frozen, so they cannot import this module, and this change "
                    + "removes none of their private copies. This module has zero consumers "
                    + "today. It does not promise to prevent a future copy.")),
            Paragraph(Text(
                "Name-shaped search also misses relevant prior art. The public theorem "
                    + "D5/S3/TotalVariation/Metric.total_variation_triangle treats finite total "
                    + "variation of real vectors. The same module publicly names "
                    + "total_variation_eq_sup_event_gap for its event-supremum characterization, "
                    + "the closest concept hit. "
                    + "MeasurableDeficiencyTriangle publicly names a deficiency triangle while "
                    + "keeping this measurable-total-variation triangle private.")),
            Paragraph(Text(
                "None of that prior art subsumes this theorem. The first two results are "
                    + "stated for a Fintype and real-valued functions, and the event-supremum "
                            + "one additionally assumes equal total mass, whereas this result "
                    + "admits arbitrary, possibly infinite measures.")),
            Paragraph(Text(
                "Pinned Mathlib was searched by name and by concept. The relative used by the "
                    + "proof is tsub_le_tsub_add_tsub. The search found no upstream statement of "
                    + "this triangle law; that reports the search result and does not say that "
                    + "no upstream form can exist.")),
            Paragraph(Text(
                "The repository also re-derives symmetry twice: once as a private named theorem "
                    + "in MeasurableDescentErrorBounds, and once inline, as the same simp call, "
                    + "inside a calculation in MeasurableDeficiencyTriangle. An earlier draft "
                    + "counted only declaration names, found one occurrence, and excluded "
                    + "symmetry on that basis. A review seat found the inline occurrence. "
                    + "Counting names undercounts duplication.")),
            Paragraph(Text(
                "The value is API, not mathematical novelty. The general lemma proves an "
                    + "order-theoretic bound at a fixed index and lifts it to the suprema. The "
                    + "measure theorem is a single instantiation. Symmetry is one simp call.")),
            Describe.Lean(
                DescribeId.Create("isup-max-tsub-triangle"),
                DeclarationHandle.Create(DeclarationPrefix + "iSup_max_tsub_triangle"),
                H("Indexed truncated differences satisfy the triangle bound"),
                StatementSource.FromAuthor(ISupMaxTsubTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Index is an arbitrary type, with no Fintype or measurable structure. The "
                        + "three functions f, g, and h are arbitrary ENNReal-valued families, "
                        + "and there are no hypotheses. At each index, the two directed "
                        + "truncated differences are bounded through g; each term is then "
                        + "lifted to its corresponding supremum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("measurable-total-variation-triangle"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "measurable_total_variation_triangle"),
                H("Measurable total variation satisfies the triangle inequality"),
                StatementSource.FromAuthor(MeasurableTotalVariationTriangleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any measurable space and any three measures mu, nu, and rho, with no "
                        + "finiteness, probability-normalisation, or other hypotheses, this is "
                        + "the general lemma instantiated on measurable events."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("measurable-total-variation-comm"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "measurable_total_variation_comm"),
                H("Measurable total variation is symmetric"),
                StatementSource.FromAuthor(MeasurableTotalVariationCommFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any measurable space and any two measures mu and nu, with no "
                        + "hypotheses, exchanging the directed truncated differences leaves "
                        + "their maximum and hence mTV unchanged. The proof is one simp call."))),
                DescribeRole.Theorem))));

    private static Formula ISupMaxTsubTriangleFormula()
    {
        Formula indexType = F.Id("Index");
        Formula index = F.Id("i");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula h = F.Id("h");
        Formula familyType = new Formula.TypeArrow(indexType, F.Id("ENNReal"));
        Formula fh = IndexedSupremum(index, indexType, SymmetricGap(f, h, index));
        Formula fg = IndexedSupremum(index, indexType, SymmetricGap(f, g, index));
        Formula gh = IndexedSupremum(index, indexType, SymmetricGap(g, h, index));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, indexType, Colon, Sp, F.Id("Type"), Comma),
            Seq(
                Forall, Sp, f, Comma, Sp, g, Comma, Sp, h, Colon, Sp,
                familyType, Comma),
            Seq(fh, Sp, Leq, Sp, fg, Sp, Plus, Sp, gh, Dot),
        ]));
    }

    private static Formula MeasurableTotalVariationTriangleFormula()
    {
        Formula carrier = F.Id("A");
        Formula mu = F.Id("mu");
        Formula nu = F.Id("nu");
        Formula rho = F.Id("rho");

        return Disp(new Formula.Aligned([
            MeasurableCarrierLine(carrier),
            Seq(
                Forall, Sp, mu, Comma, Sp, nu, Comma, Sp, rho, Colon, Sp,
                MeasureType(carrier), Comma),
            Seq(
                MeasurableTotalVariation(mu, rho), Sp, Leq, Sp,
                MeasurableTotalVariation(mu, nu), Sp, Plus, Sp,
                MeasurableTotalVariation(nu, rho), Dot),
        ]));
    }

    private static Formula MeasurableTotalVariationCommFormula()
    {
        Formula carrier = F.Id("A");
        Formula mu = F.Id("mu");
        Formula nu = F.Id("nu");

        return Disp(new Formula.Aligned([
            MeasurableCarrierLine(carrier),
            Seq(
                Forall, Sp, mu, Comma, Sp, nu, Colon, Sp,
                MeasureType(carrier), Comma),
            Seq(
                MeasurableTotalVariation(mu, nu), Sp, Eq, Sp,
                MeasurableTotalVariation(nu, mu), Dot),
        ]));
    }

    private static Formula MeasurableCarrierLine(Formula carrier) =>
        Seq(
            Forall, Sp, carrier, Colon, Sp, F.Id("Type"), Comma, Sp,
            Typeclass(Apply(F.Id("MeasurableSpace"), carrier)), Comma);

    private static Formula IndexedSupremum(
        Formula index,
        Formula indexType,
        Formula body) =>
        Seq(
            Operatorname, Grp(F.Id("sup")),
            Underscore, Grp(index, Colon, Sp, indexType), Sp,
            body);

    private static Formula SymmetricGap(
        Formula left,
        Formula right,
        Formula index)
    {
        Formula leftValue = Apply(left, index);
        Formula rightValue = Apply(right, index);

        return Seq(
            Max, Open,
            TruncatedSubtract(leftValue, rightValue), Comma, Sp,
            TruncatedSubtract(rightValue, leftValue), Close);
    }

    private static Formula TruncatedSubtract(Formula left, Formula right) =>
        Apply(F.Id("tsub"), left, right);

    private static Formula MeasurableTotalVariation(Formula left, Formula right) =>
        Apply(F.Id("mTV"), left, right);

    private static Formula MeasureType(Formula carrier) =>
        Apply(F.Id("Measure"), carrier);

    private static Formula Typeclass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
