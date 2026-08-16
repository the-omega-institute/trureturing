using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ContractionGeometry;

internal sealed class PauliTopBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The top boundary of three Pauli contraction parameters is a null set for volume.",
        H("The Pauli Top Boundary Has Zero Volume"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-pauli-top-boundary-has-zero-volume"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/ContractionGeometry/PauliTopBoundary."
                    + "pauli_top_boundary_volume_zero"),
                H("The top boundary has zero volume"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("volume"), Open, F.Id("pauliTopBoundary"), Close,
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Represent the three diagonal Pauli contraction coefficients by a real "
                        + "triple t with the sup norm, and define its top value as the square of "
                        + "that norm. The locus where the top value equals one is exactly the unit "
                        + "sup-norm sphere, equivalently the boundary of the closed unit ball.")),
                    Paragraph(Text(
                        "Mathlib proves that the boundary of a convex set in a finite-dimensional "
                        + "real normed space has zero measure for every additive Haar measure. "
                        + "Applying that theorem to the closed unit ball gives zero volume for the "
                        + "Pauli top boundary. No claim is made here about the other ordering, "
                        + "counterexample, or qubit-channel clauses in the source atom."))),
                DescribeRole.Theorem))));
}
