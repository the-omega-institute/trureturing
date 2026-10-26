using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProjectionRange;

internal sealed class ActualRangeTensorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "These declarations construct coordinate and smoothness helpers for actual complex tensor range bundles from Mathlib tensor coordinates and the existing range prebundle. The cited reversible-channel literature supplies application context; the abstract bundle construction is the repository proof.",
        H("ActualRangeTensor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smooth-range-lift"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_range_lift"),
                H("smooth range lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("A map into the actual range prebundle is smooth when its base map and ambient fiber value are smooth. The result uses the existing local Gram coordinates and the topology selected by the range prebundle."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficients-tmul"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_tmul"),
                H("coefficients tmul"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The fixed canonical complex tensor coordinate equivalence evaluates a pure tensor u tensor w at i as w(i) times u. This algebraic identity is consumed by the tensor chart and coefficient calculations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficients-map"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_map"),
                H("coefficients map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("Canonical tensor coefficients commute with a complex linear map on the first factor. The proof checks zero, pure tensors and addition, preserving the complete tensor product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coefficients-expand"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coefficients_expand"),
                H("coefficients expand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("Every tensor is the finite sum of its first-factor coefficients tensored with the standard complex Euclidean basis. This exact expansion is used to prove smoothness of the actual tensor equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinates-into-range"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.coordinates_intoRange"),
                H("coordinates intoRange"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The coordinate map after the inverse chart map is the identity over the original column-chart base set. It follows on the full tensor product from the original range coordinate inverse law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("into-range-coordinates"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.intoRange_coordinates"),
                H("intoRange coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The inverse chart map after coordinates is the identity in each actual tensor fiber over the chart base set. No global frame or trivialization is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symm-eq"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.symm_eq"),
                H("symm eq"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The inverse of the tensor pretrivialization over its base set is exactly the stated base point together with the tensor inverse coordinate map. This supplies the formula used in smooth overlap calculations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transition-apply"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.transition_apply"),
                H("transition apply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The overlap map of the actual tensor charts is the original range transition tensored with the identity on the Euclidean factor. The result identifies the full chart maps, retaining the canonical tensor norm and inner product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth-coefficient"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_coefficient"),
                H("smooth coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("Every ambient canonical tensor coefficient is a smooth function on the actual tensor total space. The proof uses the selected range charts and their smooth transition matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("smooth-tensor-sum"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/ActualRangeTensor.smooth_tensor_sum"),
                H("smooth tensor sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("A finite family of ambient-smooth sections over a smooth base map gives a smooth total-space map into the actual tensor bundle by summing u_i tensor e_i. The source manifold is arbitrary, and zero rank and empty bases are included."))),
                DescribeRole.Theorem))));
}
