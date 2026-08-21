using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class TransientObservableFilterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite pullback observables form a descending fiber filtration with exact image and rank dimensions.",
        H("Transient Observable Filter"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("transient-observable-filter"),
                DeclarationHandle.Create(
                    "D5/S3/ContinuousObservables/TransientObservableFilter.transient_observable_filter"),
                H("Finite pullback observables have exact fiber and rank dimensions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("transientObservableFilter")), Open,
                    F.Id("tau"), Comma, Sp, F.Id("k"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier and a self-map tau, the k-step pullback image is "
                        + "a unital commutative subalgebra of the source function space. The next image "
                        + "is contained in it, and membership is exactly constancy on fibers of tau iterated k times.")),
                    Paragraph(Text(
                        "The algebra is constructed from pointwise evaluation along tau. Its dimension is "
                        + "identified by restriction to the actual image of the iterated state map, and the "
                        + "canonical transfer operator supplies the matching range rank and image cardinality."))),
                DescribeRole.Theorem))));
}
