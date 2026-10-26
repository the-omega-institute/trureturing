using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision;

internal sealed class LatticeHalfFockChargedCollisionKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged collision kernel.",
        H("Charged collision kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-collision-unit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionUnit"),
                H("The normalized square-root unit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("collisionUnit is the unit of PowerSeries Complex whose value "
                    + "is one half times (binomialSeries(1/2)+1). Its constant coefficient is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar"),
                H("Every scalar Taylor coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a,B:Int and N:Nat, collisionScalar a B N is coefficient N "
                    + "of binomialSeries(a/2) multiplied by collisionUnit^(-2*B). The signed integer "
                    + "power is taken in the power-series unit group."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-oscillator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionOscillator"),
                H("The finite oscillator coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, sigma,tau:Charge D, N:Nat and e:Int, "
                    + "collisionOscillator D sigma tau N e is a Complex-linear endomorphism of "
                    + "Oscillator D. It first applies the actual pairTranslation and then evaluates "
                    + "each translated monomial by the finite creator sum described above. "
                    + "Polynomial coefficients and repeated-variable multiplicities are retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-tensor-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionCoefficient"),
                H("The complete actual tensor coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D, "
                    + "N:Nat and e:Int, collisionCoefficient D hu sigma tau N e is chargeScalar "
                    + "D (sigma+tau) times TensorProduct.map of collisionOscillator D sigma tau N e "
                    + "and the chosen groundAction D hu (sigma+tau). Thus it acts on arbitrary "
                    + "oscillator and ground inputs and extends linearly to every ActualTensor D hu."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-field"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionField"),
                H("The pointwise lower-truncated collision field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For D:LatticeData, hu:IsUnit D.G.det, sigma,tau:Charge D "
                    + "and N:Nat, collisionField D hu sigma tau N is the NativeField with signed "
                    + "coefficient collisionCoefficient D hu sigma tau N. Its lower bound depends "
                    + "on the actual input. For p tensor g one bound is -Q(sigma+tau)-2*N minus "
                    + "the largest d(0)+d(1) in the support of pairTranslation(p); tensor induction "
                    + "extends this bound to arbitrary inputs. Endomorphism support is not assumed finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-bare-source-product"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.bare_source_product"),
                H("The ordinary charged ground-source mode"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordinary Carrier source product retains epsilon(sigma,tau), the signed creation degree -r-1-bilinear(sigma,tau), and both charges. It is consumed by the source-iterate comparison."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-chargeinsertion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion"),
                H("The finite charge insertion field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The charge-weighted singleton insertion and the finite neutral-mode correction use the actual source frequency bound. No bound on Taylor order is assumed."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-corrected-creation-step"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.corrected_creation_step"),
                H("The corrected creation step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Physical translation and the ordinary creation recurrence give the signed coefficient step on every ActualTensor input, with the actual charge insertion term."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-diagonalterm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonalTerm"),
                H("One signed creator summand"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar Taylor coefficient multiplies the two signed half-creation coefficients. Negative creator degrees are retained and vanish through the existing constructors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-diagonal-as-sum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.diagonal_as_sum"),
                H("The finite creator diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer finsum is zero at negative total degree and otherwise equals the finite natural interval sum. This supplies the support bound used by the current and finite-balance calculations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-collisiondiagonal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionDiagonal"),
                H("The translated creator diagonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two translation degrees determine the signed total. Its nonnegative branch sums every allowed creator split and its negative branch is zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collisionconvolution"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionConvolution"),
                H("The linear finite-polynomial readout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient-linear equivalence and Finsupp.lsum evaluate each pair polynomial with its own finite support. The current calculation applies it to transformed polynomials."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collision-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collision_expansion"),
                H("The actual translated-input expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The oscillator endomorphism expands over the actual pairTranslation support, with a finite signed creator diagonal for each translated monomial."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-translateddegree"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.translatedDegree"),
                H("The input translation bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supremum of the two translation degrees is taken over the finite support of the actual translated input. This bounds the negative current branch without any global End-valued support assertion."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-normalcurrent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.normalCurrent"),
                H("The charge-weighted normal current"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The current is the charge-weighted sum of singletonLinear insertions. It acts on whole fields, including coefficients evaluated on current-transformed inputs."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collisionr"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionR"),
                H("The reciprocal normalized square-root unit coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient halfBinomial(j)/(j+1) is shared by the scalar Taylor recurrence, source insertion identity, and all-order comparison."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-collisionscalar-recurrence"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.collisionScalar_recurrence"),
                H("The scalar Taylor recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Differentiating the binomial series and normalized square-root unit gives the recurrence for all signed scalar parameters and every natural order. It is the scalar input to the finite oscillator balance."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-source-neutral-creation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.source_neutral_creation"),
                H("Ordinary current action on the creation source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zero neutral mode pairs with sigma+tau. Positive modes pair with sigma and shift the ordinary creation degree, retaining negative shifted degrees through the signed constructor."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-chargeinsertion-field-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel.chargeInsertion_field_identity"),
                H("The whole-field insertion identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual insertion constructor equals the normal current minus the norm and finite bilinear corrections. Source support is padded using both the original frequency bound and the Taylor degree, without assuming either bounds the other."))), DescribeRole.Theorem))));
}
