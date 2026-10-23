using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockNestedQForwardEdgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual forward nested-Q collision equality is closed on the empty inner-cutoff branch.",
        H("Forward Nested-Q Empty-Cutoff Branch"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-weighted-identity-of-cutoff-le-lift"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift"),
                H("The forward weighted identity when the inner cutoff is at most the signed lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For arbitrary lattice data, determinant-unit witness, current label, source states, signed gamma, delta, d, r, n, actual input x, linear functional phi, finite numerator P and independent outer cutoff function H₂, assume K ≤ r. The exact second component of the nested-Q telescope is proved: the actual outer sum over j is empty because its range is ((K:ℤ)-r).toNat.")),
                    Paragraph(Text("The right-hand finite Taylor sum is also zero. If the total degree is negative its range is empty. Otherwise every u in the degree range satisfies 0 ≤ degree-u, and K ≤ r gives degree-u+r-K ≥ 0, so orderedResidueWeight is zero. The proof keeps the complete actual qField expression and arbitrary P; it does not transfer a cutoff to a Laurent monomial or assert the nondegenerate local-coordinate bridge.")),
                    Paragraph(Text("The four-slot source-bound audit remains unfinished at issue #20163; this source bridge is not declared_validated."))),
                DescribeRole.Theorem))));
}
