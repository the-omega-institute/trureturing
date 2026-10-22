using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class NativeReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original corrected charged fields admit an exact native source reflection for every finite positional oscillator word and integer coefficient.",
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
                    Paragraph(Text("The singleton identity is included in the arbitrary positional-word reflection below. Identification of the finite source reflection with ordinary conformal descendants requires the actual Sugawara one-mode action, including its zero-current endpoint. The existing stress transpose, rank/16 correction, two-sided inverse-Gram hypotheses for nondegeneracy, actual theta, odd target and integer native grading are unchanged. Full twisted Jacobi, WW gluing, Monster symmetry, fusion, string theory and AdS/CFT are not concluded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("originalwordsourcereflection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/NativeReflection.original_word_source_reflection"),
                H("Every Finite Positional Source Word"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix an arbitrary integral charge and a word of oscillator variables indexed by Fin(count). At position j let n(j)=orders(j)+1, let S be their sum, and let N be bilinear(charge,charge). Each reflected choice m(j) ranges independently from zero through n(j). The reflected source factor is C(bilinear(unitCharge(axes(j)),charge)) at m(j)=0 and X(axes(j),m(j)-1) otherwise. The coefficient is the product of choose(n(j),m(j)), with common sign (-1)^S. Its native exponent is -2*N-e-2*S-2*sum(m(j)). Both paired native states and e are arbitrary. Empty words, equal axes, repeated variables and vanishing endpoint scalars remain included.")),
                    Paragraph(Text("The flat-term proof follows the original recursive negative and positive mode split. Transposition reflects each integer mode to -mode-1 and exchanges the branch. It does not commute opposite-sign currents, so this step introduces no extra contraction. Explicit equivalences between the recursive mode-tuple types preserve the complete positional word. The existing flatTerm_finite and flatTerm_support_bound supply support witnesses before any finsum is exchanged with a finite reduction sum.")),
                    Paragraph(Text("The correction substitution fixes the central shift variable and sends each oscillator jet to its finite reflected-jet expansion. The independent-order pairScalar_reflection lifts to the original pair polynomials and proves the pair-derivation chain rule. Together with singleton_correction_reflection it intertwines the original insertion operators. Induction on the labelled word therefore preserves all labelledRemainders multiplicities of correctionWord, including repeated factors.")),
                    Paragraph(Text("Normal-order evaluation is linear. It is applied through its central-shift and variable-insertion identities, without asserting that it preserves arbitrary products. Weighted homogeneity gives the common coefficient shift; the original groundReflection supplies nativeOppositeYtw. The charged field, chargeScalar, cocycle and native bilinear pairing retain their original definitions.")),
                    Paragraph(Text("The statement is an exact algebraic transpose for the original corrected native fields. It does not conclude twisted Jacobi, Moonshine gluing, fusion, string theory or an AdS/CFT correspondence."))),
                DescribeRole.Theorem))));
}
