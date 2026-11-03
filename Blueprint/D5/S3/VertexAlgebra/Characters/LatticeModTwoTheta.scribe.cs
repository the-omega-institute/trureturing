using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeModTwoThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original mod-two charge fibres are identified with the actual discriminant sectors of the doubled Gram form. This classical lattice construction transports the existing sector S and T laws; it does not prove a second Poisson or sector S theorem.",
        H("Original mod-two charge-fibre theta bridge"),
        Blocks(
            Paragraph(Text("The input is the original even integral LatticeData D, an integral unit determinant, and positive definiteness of gramReal D. All natural ranks, including zero, every original mod-two charge, and the whole upper half-plane remain in scope. The lattice conventions and modular suppliers are those of LatticeDiscriminantTheta and LatticeDiscriminantWeil; the signs are the original cocycle-derived OriginalFourMChargeCoset signs. No novelty claim is made for these classical mathematical statements.")),
            Describe.Lean(
                DescribeId.Create("latticemodtwotheta-gram2g"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.Gram2G"),
                H("Doubled original Gram form"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep the original rank and multiply the original integral Gram matrix by two. Symmetry and evenness are constructed directly."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticemodtwotheta-charge-lift"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.chargeLift"),
                H("Integral lift of the original parity charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the actual ZMod 2 value in each original coordinate as an integer. This is a representative, not an additive section."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticemodtwotheta-phi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.phi"),
                H("Actual additive quotient equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The class of G times the integral lift defines an AddEquiv from the original mod-two charges to Z^rank / (2G) Z^rank. The integral inverse of the unimodular Gram matrix proves bijectivity. Equality of classes is exactly equality of the original reductions modulo two."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticemodtwotheta-parity-theta"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.parityTheta"),
                H("Literal unbounded original charge fibre"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum exp((pi i tau / 2) times bilinear D p p) over the original subtype reduceCharge D p = a. The definition includes negative integer charges and does not use a discriminant-sector theta."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticemodtwotheta-original-bridge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeModTwoTheta.original_modTwo_theta_bridge"),
                H("Quotient, phases, convergence and exact modular transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive unimodularity gives det G = 1 and det(2G) = 2^rank. The rational inverse of 2G sends Gp to p/2; its pairing on Gp,Gq is bilinear D p q divided by two and its quadratic value is bilinear D p p divided by four. Actual two-torsion removes the negative Fourier character, yielding the unchanged original fourierSign; the original cocycle energy yields quadraticSign. The bijection n maps to 2n + lift(a) parametrizes the literal fibre, giving absolute convergence and equality to sectorTheta (Gram2G D) (phi a). Consuming the frozen sector_S and sector_T gives the principal complex factor (-i tau)^(rank/2) / sqrt(2^rank) and the original signs, without an additional phase, branch, parity or positive-rank premise.")),
                    Paragraph(Text("This is only the charge-coset modular supplier. OriginalFourMChargeCoset.cosetKernel still contains both chargeScalar factors 2^(-norm p), the half-average with theta reflection, the oscillator kernels and the inverse-Gram/factorial dual oscillator monomial. Their coefficient transport and the homogeneous parity-state premises of the actual fourM/Jacobi use remain work. No unrestricted identityK, original full crossing, Monster realization, full VOA/CFT, string theory or AdS/CFT completion is asserted."))), DescribeRole.Theorem))));
}
