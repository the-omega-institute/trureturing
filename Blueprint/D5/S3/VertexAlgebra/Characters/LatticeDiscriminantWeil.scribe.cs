using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantWeilDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal shifted theta series of every positive even integral lattice transforms by its actual discriminant pairing. Negative Fourier operators on all functions satisfy the phased Weil relations, and the original positive Gaussian fixes the Milgram phase. All natural ranks are included. No fusion, Monster, sewing, CFT, string or AdS realization is asserted.",
        H("Original lattice discriminant S, Weil and Milgram laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-rho"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.rho"),
                H("Positive cardinal normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar rho is the complex cast of the positive real square root of the cardinality of the actual Gram cokernel. Positivity of the original real Gram matrix identifies its square with det G and makes rho nonzero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-weils"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilS"),
                H("Negative Fourier operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On every complex function f on the original discriminant A, S f at a is rho inverse times the sum over b of exp(-2 pi i B(a,b)) f(b). This is a complex linear endomorphism on the whole function space."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-weilsplus"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilSplus"),
                H("Positive Fourier inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive Fourier operator has kernel exp(+2 pi i B(a,b)) divided by rho. It is both a left and a right inverse of the negative operator on every function."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-weilt"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.weilT"),
                H("Original half-norm operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex linear operator T multiplies f(a) by exp(2 pi i q(a)), where q is the half norm of the original even integral Gram lattice modulo integers."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-chargeconjugation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.chargeConjugation"),
                H("Charge conjugation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex linear operator C sends f(a) to f(-a) on every complex function. No evenness assumption is imposed on f."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-gaussphase"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.gaussPhase"),
                H("Positive normalized Gauss sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual finite discriminant, gamma is rho inverse times the sum of exp(+2 pi i q(a)) over every class a. The positive sign is part of this definition."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-sector-s"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.sector_S"),
                H("All original shifted sectors under inversion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original LatticeData D with positive real Gram matrix, every discriminant class a and every tau with positive imaginary part, Theta_a(-1/tau) equals (-i tau) to the principal power rank/2, divided by sqrt(det G), times the sum over c of exp(-2 pi i B(a,c)) Theta_c(tau). Coordinate Poisson summation applies to the literal translated Gaussian. Translation has a positive Fourier phase; integer negation converts the absolutely convergent dual sum to the existing negative inverse coefficient. Compact normal convergence is transported through the translated compact set, including empty sets and rank zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-finite-weil-relations"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations"),
                H("Full function-space Weil identities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original positive even integral lattice, rho is nonzero and rho squared is the discriminant cardinality. On the whole complex function space, S squared equals C, S to the fourth equals the identity, and both products S Splus and Splus S equal the identity. With composition S after T, (S T) cubed equals gamma C. Character orthogonality and a finite completed-square identity prove these relations independently of theta values. These are phased relations; they do not assert an unphased modular representation or isometry for the supremum norm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticediscriminantweil-milgram"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.milgram"),
                H("Milgram phase of the original positive even lattice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural rank, the positive normalized Gauss sum of the original positive even integral Gram lattice equals exp(pi i rank/4). The actual theta S and T transformations along i, (-1+i)/2, -1+i and i combine with the full-space cubic relation. The principal logs of 1-i and (1-i)/2 add to Log(-i), giving exp(-pi i rank/4) for the product of weight factors. Representative independence identifies the original zero sector at i with a convergent positive real Gaussian sum; its zero-vector term is one, so its real part is at least one. Cancelling this nonzero original theta value fixes the positive phase. No positive-rank, even-rank or diagonal restriction is imposed."))), DescribeRole.Theorem))));
}
