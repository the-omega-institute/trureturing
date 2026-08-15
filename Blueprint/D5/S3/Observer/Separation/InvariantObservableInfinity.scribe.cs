using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class InvariantObservableInfinityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded invariant observable separating two points forces infinite observer distance.",
        H("Invariant Separation Forces Infinite Observer Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invariant-separation-forces-infinite-observer-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/InvariantObservableInfinity."
                        + "invariant_separation_distance_eq_top"),
                H("Invariant separation forces infinite observer distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Bounded")), Open, F.Id("f"), Close, Comma, Sp,
                    F.Id("L"), Underscore, Tau, Open, F.Id("f"), Close, Sp, Eq, Sp, D(0),
                    Comma, Sp,
                    F.Id("f"), Open, F.Id("x"), Close, Sp, Neq, Sp,
                    F.Id("f"), Open, F.Id("y"), Close, Sp, Rightarrow, Sp,
                    F.Id("d"), Underscore, Tau, Open, F.Id("x"), Comma, Sp,
                    F.Id("y"), Close, Sp, Eq, Sp, Infty, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be a bounded complex observable on the update index set. Its "
                            + "update defect L_tau(f) vanishes exactly when f is invariant under "
                            + "the permutation. If f separates x and y, their endpoint gap is "
                            + "strictly positive.")),
                    Paragraph(Text(
                        "Every natural-number multiple of f remains bounded and has zero update "
                            + "defect, hence remains in the unit admissible ball. The corresponding "
                            + "endpoint gaps are unbounded, so their ENNReal supremum is infinity. "
                            + "The theorem uses the repository's frozen update-defect definition; "
                            + "the nearby visible-phase result is a concrete solenoid instance of "
                            + "this general scaling mechanism."))),
                DescribeRole.Theorem))));
}
