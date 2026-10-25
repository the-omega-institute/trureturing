using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class ActualChargedAdjointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Tensor Charged Bilinear Adjoint", H("Actual Tensor Charged Bilinear Adjoint"), Blocks(
            Paragraph(Text("The ground module is exactly the already selected ActualGround D hu, defined using the existing Classical.choose actual twisted ground representation. A GroundPairing is chosen from actual_ground_pairing, and actualForm is the tensor product of its complex bilinear form with SignedOscillatorWick.wick. The ground pairing may be nonsymmetric. This module proves and uses no symmetry assertion.")),
            Paragraph(Text("On pure tensors the existing charge scalar 2^(-N) is retained. The actual same-charge ground signed adjoint contributes paritySign(N/2), and the oscillator rectangle contributes exponent -e-2N. Tensor induction gives the full statement B(C(a,e)x,y)=paritySign(N/2)B(x,C(a,-e-2N)y) for arbitrary actual tensor inputs. No positivity, rank restriction, Jacobi, covariance or desired adjoint premise is supplied.")),
            Paragraph(Text("Tensor nondegeneracy uses a finite basis of the actual ground coordinate space, its dual basis for G, and a different dual basis for G.flip. These isolate the two tensor slots separately. No symmetry-dependent right-dual identity and no infinite-dimensional full-dual isomorphism is used.")),
            Paragraph(Text("The full algebraic dual coefficient on charged generators is a genuine consumer: for each charge and each nonzero actual ground u, tensor nondegeneracy detects the existing charged_ground_leading at exponent -N. The proved actual adjoint moves that nonzero test into the first coefficient slot, retaining its parity sign. The original corrected-source consumer uses this result. Restricted-dual representability, full corrected adjointness, a two-twisted intertwining field, mixed Jacobi, fusion and the complete Monster/string/AdS objective remain open. Classical construction; no novelty claim.")),
            Paragraph(Text("Information-escape registration remains unfinished: the faithful compiled Reg mirrors currently report declared_unresolved. The source-reconstruction diagnostics and missing binding certificates are recorded at https://github.com/the-omega-institute/trureturing/issues/21134 under the repository linked-issue exception. Compilation does not assert a validated registration.")),
            Describe.Lean(DescribeId.Create("actual-form"),
                DeclarationHandle.Create(Prefix + "actualForm"),
                H("actualForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Tensor form on the original ActualTensor, using the exact chosen actual ground and the signed oscillator Wick form."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-charged-coefficient-adjoint"),
                DeclarationHandle.Create(Prefix + "actual_charged_coefficient_adjoint"),
                H("actual charged coefficient adjoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The unrestricted same-charge signed adjoint at the exact reflected integer exponent -e-2*bilinear D a a. Both tensor inputs are actual twisted tensors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-form-nondegenerate"),
                DeclarationHandle.Create(Prefix + "actualForm_nondegenerate"),
                H("actualForm nondegenerate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Both-sided tensor nondegeneracy is proved by finite coordinate isolation using G.dualBasis and G.flip.dualBasis separately."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("charged-dual-coefficient"),
                DeclarationHandle.Create(Prefix + "chargedDualCoefficient"),
                H("chargedDualCoefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Left-oriented full algebraic functional on finitely supported charged generators: the coefficient acts on the first twisted input."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("charged-dual-coefficient-nonzero-second-ground"),
                DeclarationHandle.Create(Prefix + "chargedDualCoefficient_nonzero_second_ground"),
                H("chargedDualCoefficient nonzero second ground"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every charge and nonzero actual ground second input, some actual first input gives a nonzero generator coordinate at exponent minus the original signed norm. It consumes the constructed adjoint, nondegeneracy and existing actual leading coefficient."))),
                DescribeRole.Theorem))));
}
