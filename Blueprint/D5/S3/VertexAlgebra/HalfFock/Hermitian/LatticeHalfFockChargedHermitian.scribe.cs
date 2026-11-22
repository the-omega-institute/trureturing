using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock.Hermitian;

internal sealed class LatticeHalfFockChargedHermitianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Chosen-Tensor Charged Field Hermitian Adjoints",
        H("Native Chosen-Tensor Charged Field Hermitian Adjoints"),
        Blocks(
            Paragraph(Text("The carrier is the literal ActualTensor(D,hu) with its unchanged nested chosen ActualGround, groundRepresentation and groundAction. The form is exactly the original tensorForm. The chargedCoefficient retains chargeScalar(D,a)=2^(-bilinear(D,a,a)), not a modified normalization. Conjugation fixes this real integral power, and replacing a by -a leaves it unchanged. The original chosen-ground signed adjoint is reused with the exact epsilon(D,a,a); group inverse is not silently identified with literal charge reflection.")),
            Describe.Lean(
                DescribeId.Create("charged-coefficient-field-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian.charged_coefficient_field_adjoint"),
                H("Actual Coefficient and Actual Existing Field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original lattice D, determinant unit proof hu, integral charge a, integer exponent M and arbitrary original tensor states v,w, tensorForm(chargedCoefficient(a,M)v,w) equals epsilon(D,a,a) times tensorForm(v,chargedCoefficient(-a,-M-2*chargeNorm(D,a))w). The theorem also states and proves the same identity for the literal existing chargedField.coeff on all targets and all coefficient exponents. There is no replacement field. On pure tensors, the proved full oscillator coefficient transpose and the original chosen-ground signed adjoint combine with the real chargeScalar. Independent tensor induction in both arguments then proves the law for arbitrary mixed finite tensors, not only separable states. The chargedField clause consumes the resulting operator law through the original HVertexOperator coefficient identity."))),
                DescribeRole.Theorem),
            Paragraph(Text("The substantive new mathematics is the full half-frequency coefficient transpose and its normal-ordered original oscillator consequence. The tensor extension, real scalar reflection, unchanged ground geometry and literal field coefficient identification are consumers, not independent novelty or bind-only credit. The raw joint theorem retains both native coefficient and existing field laws so that neither conjunct is omitted from the owning audit. Its Reg realization observes both scalar outputs and proves the equivalent full telescope, rejected variation, sensitivity and state dependence on the actual chosen carrier. The algebraic law imposes no positive-definite Gram, unitarity or primary-state hypothesis, and includes rank zero and indefinite signature wherever the original hu exists.")),
            Paragraph(Text("The full original objective remains open. This result does not prove arbitrary-first all-state Ytw BPZ/PCT, either unavailable all-j charged target, all-state twisted Jacobi or VOA gluing, Monster moonshine, fusion or anomaly completion, full string theory or AdS/CFT reconstruction. It implies no all-charge Lorentzian BRST positivity. Prior unresolved registrations, the twirl certificate and prior obligations are unchanged. Source compilation, scoped report, Scribe emission, registration admission and parent acceptance are separate evidence boundaries.")) )));
}
