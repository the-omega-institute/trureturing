using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class RefinementDistanceMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refining observables without changing old costs cannot decrease dual distance.",
        H("Observer Distance Monotonicity Under Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-distance-is-monotone-under-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/RefinementDistanceMonotonicity."
                        + "observer_distance_mono_of_refinement"),
                H("Observer distance is monotone under refinement"),
                StatementSource.FromAuthor(Disp(Seq(
                    new Formula.Subscript(F.Id("d"), F.Id("m")), Sp, Leq, Sp,
                    new Formula.Subscript(F.Id("d"), Seq(F.Id("m"), Plus, D(1))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each layer, take the supremum of the endpoint evaluation gap over "
                            + "observables in that layer whose seminorm cost is at most one. "
                            + "The distance is extended-valued, so unbounded families are retained.")),
                    Paragraph(Text(
                        "If the old observable family is contained in the refined family and the "
                            + "new seminorm restricts to the old one, every old admissible observable "
                            + "remains admissible. Pinned Mathlib's iSup_mono' compares the two "
                            + "differently indexed suprema directly."))),
                DescribeRole.Theorem))));
}
