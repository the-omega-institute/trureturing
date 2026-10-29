using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original positive even integral lattices give finite discriminant theta sectors, exact inverse theta dissection, T multipliers and finite character resolution. The zero-sector S row uses the principal complex power. No lattice-sector VOA module or physical realization is asserted.",
        H("Original lattice discriminant theta sectors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-discriminant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.Discriminant"),
                H("Original Gram cokernel"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the original integral charge lattice M = Z^d, the discriminant carrier is the actual quotient M / range(G). No finite-group data are supplied."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-dual-quotient-equiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dualQuotientEquiv"),
                H("Original dual quotient"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Inverse rational Gram coordinates identify M / G M with the quotient of the original dual lattice by the original integral lattice."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-dual-lattice-realization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.dual_lattice_realization"),
                H("Rational and real dual realization"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original LatticeData D with positive real Gram matrix, the rational dual agrees with the intrinsic integral-pairing dual, the discriminant cardinal is the absolute integral determinant, and every real vector pairing integrally with the original lattice is an inverse-Gram rational vector. Empty coordinates are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-phase"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.phase"),
                H("Faithful rational phase"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational quotient Q / Z embeds in the real additive circle and then in the complex unit circle; its value on x is exp(2 pi i x)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.pairing"),
                H("Original quotient pairing"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pairing of the classes of r and s is the class of (G_Q inverse r) dot s in Q / Z. Rational inversion takes place after extending scalars."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-quadratic-class"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.quadraticClass"),
                H("Original even half norm"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic value of the class of r is the class of r dot G_Q inverse r divided by two. Original lattice evenness makes this independent of representatives."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-discriminant-quadratic"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.discriminant_quadratic"),
                H("Nondegenerate quadratic refinement"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even integral Gram matrix, q(a+c) = q(a)+q(c)+b(a,c), q(k a) = k squared q(a) for every integer k, the pairing has zero radical, and the complex phase is injective on Q / Z."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-representative-theta"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.representativeTheta"),
                H("Literal shifted Gaussian"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any integer representative r, sum exp(pi i tau Q_G(n+G_Q inverse r)) over every original integral vector n. The rational shift is embedded in the original real coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-sector-theta"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sectorTheta"),
                H("Discriminant theta sector"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sector of an actual quotient class uses a chosen representative in the literal shifted Gaussian. No additive section is asserted."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-sector-summable-representative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_summable_representative"),
                H("Absolute convergence and representative independence"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even integral lattice, every actual class a, every integer representative r of a and every tau in the upper half-plane, the literal shifted Gaussian has summable norms and equals the sector theta function."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-inverse-theta-dissection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_dissection"),
                H("Exact inverse theta dissection"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank, original positive Gram matrix and upper half-plane tau, theta of the real inverse Gram matrix is the finite sum of all original quotient-sector theta functions. The actual charge bijection is (a,n) mapped to rep(a)+G n; absolute convergence precedes product reindexing."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-zero-sector--s"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.zero_sector_S"),
                H("Original zero-sector S row"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even integral lattice and upper half-plane tau, Theta_0(-1/tau) is (-i tau) to the principal power d/2 divided by the positive real square root of det G, times the sum of all discriminant sectors at tau. This follows from exact inverse theta dissection and matrix Gaussian inversion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-sector--t"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.sector_T"),
                H("Original class T law"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even integral lattice, every discriminant class and upper half-plane tau, Theta_a(tau+1) = exp(2 pi i q(a)) Theta_a(tau). The original even charge energy removes the integral Gaussian phase."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-character-equiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.characterEquiv"),
                H("Perfect original pairing"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nondegenerate inverse-Gram pairing and the faithful rational phase identify the actual finite discriminant carrier with its full complex character group."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-inverse-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverseCoefficient"),
                H("Actual character-weighted inverse coefficients"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each discriminant class a, sum the original inverse-form integer Gaussian weighted by exp(-2 pi i b(a,[k])). The negative sign is part of this coefficient definition."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminanttheta-inverse-theta-fourier"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta.inverse_theta_fourier"),
                H("Finite resolution and reconstruction"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even lattice and upper half-plane tau, all character-weighted inverse coefficients converge absolutely. Each is the finite sum of Theta_c weighted by exp(-2 pi i b(a,c)); conversely the sum of a coefficient weighted by exp(2 pi i b(a,c)) over all a equals natAbs(det G) times Theta_c. Orthogonality is proved for this actual quotient pairing."))), DescribeRole.Theorem))));
}
