using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class NativeSymmetricFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The chosen native Leech ground has a nonzero invariant symmetric complex-bilinear form with both radicals zero.",
        H("Symmetric Bilinear Self-Duality of the Native Ground"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nativesymmetricform"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/NativeSymmetricForm.invariant_form_unique"),
                H("Symmetric Bilinear Self-Duality of the Native Ground"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The coordinate pairing is sum_t f(t)g(t), with no complex conjugation. Pulling it back along the proved original quotient intertwiner defines nativePairing on NativeGround itself. Bilinearity is part of its Lean bilinear-form type. Symmetry follows from commutativity of complex multiplication.")),
                    Paragraph(Text("Translation permutes the summands and each binary character has square one. The original actionScalar is also a sign of square one. Consequently the pairing is invariant under every original quotient element. The coordinate pairing has both zero radicals; the genuine linear equivalence transports both radicals to zero in the original native carrier.")),
                    Paragraph(Text("For any invariant bilinear form C, its comparison endomorphism T is characterized by B(Tu,v)=C(u,v). Invariance of both forms makes T commute with all actual charge operators. The completed nativeOperatorAlgebra scalar commutant then implies C is a scalar multiple of B. No Schur or Burnside assertion is assumed. This is the substantive invariant_form_unique result. The preserved chosen_native_symmetric_self_duality conjunction only packages the preceding results and has no separate mathematical novelty.")),
                    Paragraph(Text("For an integral charge a the square and reflection sign is epsilon(D,a,-a)=complexSign(q(reduceCharge(a)))=paritySign(bilinear(D,a,a)/2). The exact bilinear adjoint relation is B(U_a u,v)=epsilon(D,a,-a) B(u,U_{-a}v), using the original ground_action_product rather than a sign-free reflection identity. The projector product on the same original carrier produces the orbit that defines the pairing. The construction is a ground-representation result; it does not establish twisted Jacobi, full moonshine, a string theory or an AdS/CFT realization.")),
                    Paragraph(Text("Removing a separate novelty claim does not authorize standalone bind-only retention. The chosen_native_symmetric_self_duality package has no mathematical consumer; original_integral_square and original_integral_adjoint feed only that package. The companion symmetry and nonzero statements have only aggregate or audit uses. They remain exact source progress, not independently admissible new results. The upstream positive finite certificates and the original-source audit obligations remain separate delivery boundaries; neither is resolved by changing this exposition or selecting invariant_form_unique as its truth anchor."))),
                DescribeRole.Theorem))));
}
