using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class NativeReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original corrected charged single-oscillator fields admit an exact native source reflection at every oscillator order and integer coefficient.",
        H("Native Half-Coordinate Source Reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("originaljetsourcereflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection.original_jet_source_reflection"),
                H("Every Corrected Charged Current Descendant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The source is the actual ordinaryCarrier state single(charge,X(axis,order)); both paired states are arbitrary elements of the original chosen Leech ActualTensor. The proof uses the original Corr, shiftLinear, normalInsertion and chargedField, not a supplied module action or a Jacobi or contragredient premise.")),
                    Paragraph(Text("At source order n, the reflected source contains every lower oscillator order r from 0 through n with coefficient (-1)^(n+1) times choose(n+1,r+1). Its native integer exponent is -2*chargeNorm-e-2*n-2*r-4. There is also a pure charged source, with coefficient (-1)^(n+1) times bilinear(unitCharge(axis),charge), at exponent -2*chargeNorm-e-2*n-2. This extra source term is obtained from the actual singleton correction; it is not dropped or identified with a conformal transformation by assumption.")),
                    Paragraph(Text("nativeOppositeYtw is defined on the complete original ordinary carrier by applying each original correctedPolynomial to the target after the actual groundReflection. The latter is the oscillator identity tensored with groundAction(-charge) squared. Its charged coefficient is exactly chargeScalar(charge) times the tensor map with oscillatorCoefficient of the same charge and epsilon(charge,-charge) times groundAction(-charge). Thus the original scalar and ground cocycle occur once each; the pairing is complex-bilinear, not Hermitian.")),
                    Paragraph(Text("The current mode reflects as j to -j-1 with a minus sign. The jet scalar is derived from the original half-coordinate product by the binomial-ring Chu-Vandermonde identity. No standard integer-mode derivative formula is substituted. For each lower source order, flatTerm_finite provides the target-dependent finite signed-mode support. The two-slot pairing is mapped only over a finite support, and finsum_sum_comm uses finite supports for each lower-order source before integer reflection reindexes the modes.")),
                    Paragraph(Text("This is substantive progress on the original field-invariance bridge, not complete all-state invariance. Products of two or more source oscillators require the native conformal reflection of the original pair corrections and a finite source-word compatibility theorem. Identification with the original ordinary source conformal operator also remains open. The existing stress transpose, rank/16 correction, two-sided inverse-Gram hypotheses for nondegeneracy, actual theta, odd target and integer native grading are unchanged. Full twisted Jacobi, WW gluing, Monster symmetry, fusion, string theory and AdS/CFT are not concluded."))),
                DescribeRole.Theorem))));
}
