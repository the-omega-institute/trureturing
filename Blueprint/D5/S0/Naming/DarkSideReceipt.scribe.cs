using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class DarkSideReceiptDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completing a countable metric space without isolated points makes the anonymous complement comeagre and measure one.",
        H("The Dark-Side Receipt"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("completion-dark-side-receipt"),
                DeclarationHandle.Create("D5/S0/Naming/DarkSideReceipt.dark_side_receipt"),
                H("Completion makes the anonymous complement comeagre and measure one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("MetricSpace")), Open, F.Id("N"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("Countable")), Open, F.Id("N"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("PerfectSpace")), Open, F.Id("N"), Close, Comma, Sp,
                    Neg, Operatorname, Grp(F.Id("CompleteSpace")), Open, F.Id("N"), Close, Comma, RowBreak,
                    Operatorname, Grp(F.Id("MeasurableSpace")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close, Close, Comma, Sp,
                    Operatorname, Grp(F.Id("BorelSpace")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close, Close, Comma, Sp,
                    Mu, Sp, Colon, Sp, Operatorname, Grp(F.Id("Measure")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close, Close, Comma, RowBreak,
                    Operatorname, Grp(F.Id("NoAtoms")), Open, Mu, Close, Comma, Sp,
                    Operatorname, Grp(F.Id("IsProbabilityMeasure")), Open, Mu, Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("DenseRange")), Open, F.Id("coe"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("PerfectSpace")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close, Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("IsMeagre")), Open,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("coe"), Close, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("complement")), Open,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("coe"), Close, Close,
                    InMacro, Sp, Operatorname, Grp(F.Id("residual")), Open,
                    Operatorname, Grp(F.Id("Completion")), Open, F.Id("N"), Close, Close, Sp, Land, RowBreak,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("complement")), Open,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("coe"), Close, Close, Close, Sp, Land, Sp,
                    Mu, Open, Operatorname, Grp(F.Id("complement")), Open,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("coe"), Close, Close, Close,
                    Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let N be a countable incomplete metric space without isolated points, let X be its "
                        + "metric completion, and let mu be any atomless Borel probability measure on X. "
                        + "The canonical embedding coe : N -> X has dense range by the defining property "
                        + "of completion. Density transfers the absence of isolated points from N to X.")),
                    Paragraph(Text(
                        "Every singleton in the perfect metric space X is closed with empty interior, hence "
                        + "nowhere dense. The canonical image is countable, so it is meagre and its complement "
                        + "is residual (comeagre). Since X is complete metrizable, the Baire theorem makes that "
                        + "residual complement dense and therefore nonempty.")),
                    Paragraph(Text(
                        "An atomless measure vanishes on the countable canonical image. Probability normalization "
                        + "then gives its complement measure one. The checked rational witness shows that all "
                        + "hypotheses are simultaneously realizable: Q is countable, perfect, and incomplete, "
                        + "while Lebesgue measure restricted to (0, 1] and transported across "
                        + "Completion(Q) ~= R is atomless and probabilistic."))),
                DescribeRole.Theorem))));
}
