using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockSliceQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary-cutoff homogeneous Laurent quotients for the actual nested-Q distribution.",
        H("Homogeneous slice quotient compatibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-slice-quotient-compat"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient.actual_slice_quotient_compat"),
                H("The supplied numerator and the locality supplier define the same rational slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For the exact actual JAB distribution and the coefficient telescope of sameNumeratorCollisionBridge, let P and P₀ be finite Laurent polynomials at arbitrary natural cutoffs K and K₀. Their signed total degrees are L+M+K-d-r-n-3 and L+M+K₀-d-r-n-3. Neither cutoff is required to be a source/source locality witness. With C=v-z and T=max K K₀, the theorem proves C^(T-K) P=C^(T-K₀) P₀, and equality of P/Q_K and P₀/Q_K₀ in the common rational field.")),
                    Paragraph(Text("Multiplication by a labelled difference translates a scalar homogeneous slice by exactly one degree. Iterating this finite coefficient identity, and composing the polynomial actions on the same actual distribution, puts both numerators on the identical degree slice at T. The three labelled differences are nonzero, so the common denominator is nonzero. All global Laurent exponents remain signed; negative total degree, zero numerators, and K=0 remain in scope. No support assertion is imposed on the whole distribution.")),
                    Paragraph(Text("The comparison is consumed in the same theorem by the actual complete left and swapped current/second-source local readouts. The actual supplier's quotient is transported to the supplied P/Q_K, retaining arbitrary output mode, input tensor, linear functional, signed indices, and independent outer cutoffs. The supplied complete-field locality laws also transport their complete outer-residue support and cutoff-padding statements. These are statements about complete two-order residues.")),
                    Paragraph(Text("The exact local rational normal form and joint finite Taylor support are further obligations. In the swapped branch, the expected joint support is alpha+a+k=M-j-1 and alpha+a+beta+b=degree; establishing that support and its local coefficient map is necessary before the final Taylor convolution. In the forward branch, the complete inner A/B rational residue and its pole bound L+M+(K-r-j-1).toNat remain necessary. The quotient comparison alone proves none of the three final Taylor identifications."))),
                DescribeRole.Theorem))));
}
