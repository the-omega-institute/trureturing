using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class MetricEntourageCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Metric entourages compose within the entourage at the sum of radii.",
        H("Metric Entourage Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("metric-entourage-composition-subset"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometryLaws/MetricEntourageComposition."
                        + "metric_entourage_comp_subset"),
                H("Metric entourage composition is bounded by the summed radius"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a pseudometric state carrier, the source entourage at radius "
                            + "epsilon consists of pairs whose distance is at most epsilon, "
                            + "and relation composition exposes an intermediate state.")),
                    Paragraph(Text(
                        "If the first and second legs have bounds epsilon and delta, "
                            + "the metric triangle inequality bounds the composite leg by "
                            + "epsilon plus delta."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var content = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }

            content.Add(arguments[index]);
        }

        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X");
        Formula pseudoMetric = Seq(
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")),
            Open, carrier, Close, CloseBracket);
        Formula epsilon = F.Id("epsilon");
        Formula delta = F.Id("delta");
        Formula entourage = F.Id("metricEntourage");
        Formula compose = F.Id("relationCompose");
        Formula left = Apply(entourage, epsilon);
        Formula right = Apply(entourage, delta);
        Formula composite = Apply(compose, left, right);
        Formula sum = Seq(epsilon, Sp, Plus, Sp, delta);
        Formula target = Apply(entourage, sum);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            pseudoMetric, Comma, Sp,
            Forall, Sp, epsilon, Comma, Sp, delta, Colon, Sp, F.Id("Real"), Comma, Esc,
            composite, Sp, Subseteq, Sp, target, Dot));
    }
}
