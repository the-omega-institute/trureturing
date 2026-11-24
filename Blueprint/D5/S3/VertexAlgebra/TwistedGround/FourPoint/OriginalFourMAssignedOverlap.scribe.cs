using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMAssignedOverlapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charge sums in independent native mode assignments",
        H("Marked coefficients and the signed Fourier overlaps"),
        Blocks(
            D("four-m-assigned-charge-term", "assignedChargeTerm", "Assigned charge summand",
                DescribeRole.Definition,
                Text("Multiply the inverse twelfth power of the chart period and the chart charge "
                    + "exponential by the physical partition sum of the marked word. In each partition "
                    + "the correction endpoints carry the lifted scales and four puncture contraction "
                    + "factors. The surviving endpoints are evaluated by the independent mode "
                    + "assignments of the native Wick word.")),
            D("four-m-assigned-sector", "assignedSector", "Assigned charge sector",
                DescribeRole.Definition,
                Text("Sum the assigned charge summand over all charges reducing to the prescribed "
                    + "mod-two class.")),
            D("four-m-assigned-charge-has-sum", "assigned_charge_hasSum", "Assigned sum of a marked coefficient",
                DescribeRole.Theorem,
                Text("Assume unit Gram determinant, positive definite real Gram form, a finite "
                    + "decidable label type and a word without repeated labels. At a real argument "
                    + "strictly between zero and one, use either A or B with slit parameter of norm "
                    + "less than one, or the true D lip. The charge sum on each mod-two fibre has "
                    + "sum equal to the physical product's marked Taylor coefficient at the origin. "
                    + "The copied labels have spatial degrees on the left and mark degree one on the right.")),
            D("four-m-assigned-charge-summable-norm", "assigned_charge_summable_norm",
                "Absolute summability of assigned charges", DescribeRole.Theorem,
                Text("Under the same lattice, chart and distinct-label hypotheses, the norms of "
                    + "the assigned charge terms are summable on each mod-two fibre.")),
            D("four-m-assigned-fourier-overlap", "assigned_fourier_overlap",
                "Signed overlaps of assigned charge sectors", DescribeRole.Theorem,
                Text("Assume also rank 24 and an A-parameter square root of norm less than one. "
                    + "Use the upper chart selection throughout. D in class a is the Fourier sum "
                    + "of the A sectors with signs at (a,b) and factor 2⁻¹². B is the corresponding "
                    + "sum with the additional quadratic sign of b and the inverse twelfth power "
                    + "of the A period root.")))));

    private static DocumentBlock D(string id, string name, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
