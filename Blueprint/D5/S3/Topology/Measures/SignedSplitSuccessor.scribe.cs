using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class SignedSplitSuccessorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/SignedSplitSuccessor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dynamic measured closed split with every-choice signed convergence and scheduled separation.",
        H("Dynamic measured signed split"),
        Blocks(
            Describe.Lean(DescribeId.Create("measured-dynamic-split"), DeclarationHandle.Create(Owner + "exists_measured_dynamic_split"),
                H("Dynamic measured closed split"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Starting from the empty history, the measured column construction is iterated without changing earlier entries. Its geometric-series small-mass invariant supplies the strict margins at the next target choice. Stable entries give strictly increasing target and row indices. An earlier auxiliary support belongs to every later active exclusion, so the selected later H avoids it.")),
                    Paragraph(Text("The closed split is constructed from these same dynamic H and m, using exists_closed_split_of_ordered_exclusion. Its output includes the literal closed carrier, surjective projection, whole-support auxiliary and target traces and boundary exclusion. Rows may be finite, including a singleton distinguished new row. The signed G conclusion applies to every norm-preserving real signed lift: even target columns have side mass greater than one sixth and odd columns have exact zero, giving infinitely many witnesses of both kinds.")),
                    Paragraph(Text("Finite Boolean marginal errors control every union of test atoms. Every fixed old clopen is eventually a test, and the even prefixes increase. The published signed reference convergence theorem therefore supplies a regular represented signed limit on every fixed-label subsequence. Interleaving two choices proves that one common represented limit works for every choice. The same convergence is transferred to the actual J filter by its increasing enumeration.")),
                    Paragraph(Text("The constructed I includes the active auxiliary indices and all target n indices on the target row. The actual support and fibre identifications with that row transfer the same-index target E witnesses. Old I and J are refined one-sidedly, old N is unchanged, and the new row's N is first defined from the scheduled parity pieces. The birth reservoirs are disjoint by strict index increasingness, and old disjointness is retained. Every J meets both reservoirs infinitely often. The full fixed-clopen and new Boolean coordinate fibre condition is derived on this final ordinary I. Signed weak-star compactness constructs the new row's signed reference pools internally. Independently, compactness of probability measures extracts the target positive-variation limit from the original infinite target pool; it is not identified with the variation of a signed reference. Only after this I is fixed, norm-preserving lift existence and signed compactness construct the residual-label references on every row. Full fibre-E transfers their convergence to every choice of lifts, and their permanent parity reservoirs are then defined. Any later common-row enlargement requires its own residual initialization on the genuinely final I. The literal ordinal-prefix adapter, full CH recursion and both analytic endpoints remain outside this conclusion."))), DescribeRole.Theorem))));
}
