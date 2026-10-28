using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorScalarRadialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute scalar radial rationality of the actual canonical lattice products.",
        H("Actual scalar radial rationality"),
        Blocks(
            Paragraph(Text("Let D be integral symmetric even lattice data, with a complex matrix J satisfying both J times gramComplex(D) equals the identity and gramComplex(D) times J equals the identity. The charges alpha, beta and gamma and oscillator polynomials u,v,w,p are arbitrary, including zero and mixed-energy states. The scalar functional is the factorial readout against p after projection to charge delta=alpha+(beta+gamma). Exponent a denotes the original mode -a-1.")),
            Describe.Lean(DescribeId.Create("lattice-sector-scalar-radial-ordinary-actual-scalar-radial-rationality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorScalarRadial.ordinary_actual_scalar_radial_rationality"),
                H("One rational value in both radial chambers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There exists a natural collision order N depending only on D,J,alpha,beta,u,v. For each gamma,w there are natural A,B and a common vector power series P, chosen before p. For every p there is a finite complex polynomial R whose power-series coercion is mapSeries(readout(D,p),P), with total degree at most degreeBound(D,alpha,beta,gamma,A,B,N,p).toNat. These choices come from ordinary_actual_finite_scalar_numerator.")),
                    Paragraph(Text("Write C for the two original fields Y(inclusion(alpha,u)) and Y(inclusion(beta,v)), and phi for the scalar functional above. Embed R into the native labelled Laurent polynomial ring by substituting its two variablePolynomial generators, and multiply by the Laurent monomial X^(-A)Y^(-B) to obtain L. The common native fraction is Q=L/(X-Y)^N. The supported scalarWordCarrier of C on inclusion(gamma,w) equals orderedRationalFor(Q) both for the identity order and for the swap of labels 0 and 1. Labels remain fixed in Q; the reverse embedding already supplies the required signs.")),
                    Paragraph(Text("For any nonzero complex x,y with norm(y)<norm(x), the sum over every signed pair of integer exponents of the literal readout of product(D,alpha,beta,gamma,u,v,w,a,b), multiplied by x^a y^b, is absolutely summable and has sum eval(R)(x,y)/(x^A y^B (x-y)^N). When norm(x)<norm(y), the identical statement holds for the literal reverseProduct, with the same rational value and no extra sign. In either chamber the sum of the norms is at most laurentMajorant(L,(x,y)) times the inverse radial gap abs(norm(x)-norm(y)) to power N.")),
                    Paragraph(Text("The finite-action proof matches multiplication by (X-Y)^N with the original clear binomial convolution at every signed exponent. The finite polynomial embedding uses the genuine finitely supported natural multi-index, followed by its injective inclusion into integer label coordinates. The original inclusion_canonical identity twice identifies the actual scalar coefficients, including charge reassociation for reverse order. Cancellation takes place in the supported Hahn field, where the nonzero clearing polynomial is invertible. The existing collision_absolute_evaluation then supplies norm summability, HasSum and the radial-gap bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("The rational value depends on the chosen common series and cutoffs; no uniqueness across different such choices is asserted. The conclusion concerns scalar matrix coefficients of the actual fields. It assumes no positivity, homogeneity, vacuum specialization, rationality certificate, BPZ invariance or analytic convergence premise. Signed iterate evaluation, analytic regrouping, operator convergence, sewing, Monster realization, string theory and AdS/CFT remain separate questions.")),
            Paragraph(Text("The imported lattice-field suppliers retain their Bakalov--Kac, Matsuo--Nagatomo and Carnahan attributions. Mathlib retains its authorship and Apache license for multivariate polynomials, monoid algebras, Hahn series and vertex operators. This is a synthesis of those structures with the actual finite scalar numerator; no external-literature novelty is claimed."))),
        []));
}
