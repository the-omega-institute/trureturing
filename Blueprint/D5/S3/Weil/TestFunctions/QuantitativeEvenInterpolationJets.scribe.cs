using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class QuantitativeEvenInterpolationJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/QuantitativeEvenInterpolationJets.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite node radius, positive squared-node gap and target amplitude give actual compact even interpolants with explicit L1 derivative bounds. The construction combines the existing Lagrange realization with a finite-box seed.",
        H("Actual Even Interpolation with Arithmetic Jet Budgets"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-interpolation-coefficient-budget"),
                DeclarationHandle.Create(Prefix + "interpolationCoefficientBudget"), H("The coefficient budget"),
                StatementSource.FromAuthor(Disp(F.Id("M=2*d*V*((1+R^2)/sigma)^(d-1)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The count d is the number of distinct squared interpolation nodes. Positive sigma bounds their pairwise distance. The natural exponent d-1 is truncated at zero for the empty case."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-interpolation-jet-scale"),
                DeclarationHandle.Create(Prefix + "interpolationJetScale"), H("Finite-box derivative scale"),
                StatementSource.FromAuthor(Disp(F.Id("A=8*(2*d+3)*(R+1)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use q=2d+2 boxes and radius h=1/(4(R+1)). The finite-box scale 2(q+1)/h is exactly A."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-interpolation-jet-budget"),
                DeclarationHandle.Create(Prefix + "interpolationJetBudget"), H("An arithmetic seminorm budget"),
                StatementSource.FromAuthor(Disp(F.Id("J_s=(d+1)*M*A^(2*d+s)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is a deliberately coarse bound. The construction below proves it for s=0,1,2. The finite coefficient count and the highest derivative order are both retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("polynomial-unit-disk-coefficient-bound"),
                DeclarationHandle.Create(Prefix + "polynomial_coeff_norm_le_of_unit_disk"), H("Coefficients from a disk bound"),
                StatementSource.FromAuthor(Disp(F.Id("If |P(z)|<=M for |z|<=1, every coefficient of P has norm at most M."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse Mathlib Polynomial.fourierCoeff_toAddCircle_natCast. The Haar measure is normalized to one, and the Fourier character has unit norm. No new polynomial Cauchy or Fourier theory is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lagrange-explicit-coefficient-bound"),
                DeclarationHandle.Create(Prefix + "lagrange_coeff_le_explicit_budget"), H("Actual Lagrange coefficients are controlled"),
                StatementSource.FromAuthor(Disp(F.Id("Given |z_i|<=R, |v_i|<=V, |seed_i|>=1/2 and sigma<=|z_i^2-z_j^2| for i!=j, every coefficient of Lagrange.interpolate(z_i^2,v_i/seed_i) has norm at most M."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing GautschiEvenInterpolationBounds owner controls the interpolant on a disk. Use a square root only in the proof of disk coverage, then apply the library coefficient identity. The numerical bound itself uses finite arithmetic only. Literature anchor: Walter Gautschi, On inverses of Vandermonde and confluent Vandermonde matrices, Numerische Mathematik 4 (1962), 117-123, Section 2 (2.1) and Theorem 1 (3.1). Squared-node gaps include both direct and reflected separations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-polynomial-iterate-derivative"),
                DeclarationHandle.Create(Prefix + "evenPolynomialDifferential_iterate_deriv"), H("Exact derivatives of the existing realization"),
                StatementSource.FromAuthor(Disp(F.Id("D^s(evenPolynomialDifferential(P,psi))=sum_k coeff(P,k)*(-i)^(2k)*D^(2k+s)psi."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induct on s and use HasDerivAt.fun_sum. This is the existing interpolation constructor exposed for reuse; no second differential realization is defined."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-polynomial-actual-l1-bound"),
                DeclarationHandle.Create(Prefix + "evenPolynomialDifferential_L1_le"), H("Every derivative term is included in the L1 budget"),
                StatementSource.FromAuthor(Disp(F.Id("L1(D^s P(-D^2)psi)<=sum_k |coeff(P,k)|*L1(D^(2k+s)psi)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All derivatives are compactly supported and integrable. Apply the finite-sum triangle inequality and commute the finite sum with the integral. The powers of minus i have norm one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-interpolant-constructed-explicit-jets"),
                DeclarationHandle.Create(Prefix + "exists_even_interpolant_with_explicit_jets"), H("An actual test with no assumed jet certificate"),
                StatementSource.FromAuthor(Disp(F.Id("For a finite node family with R,V>=0 and sigma>0 satisfying the certified radius, target and squared-gap bounds, there exists a WeilTestFunction g with FT(g)(z_i)=v_i, support in [-h,h], and L1(D^s g)<=J_s for s<=2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Construct finiteBoxSeed(h,q), q=2d+2. Its transform denominator is at least one half and all required derivatives are bounded by A^k. Apply the existing Lagrange polynomial differential realization. The polynomial degree bound limits the required derivatives; the coefficient estimate supplies M. The initial smooth bump's high derivatives never appear as inputs.")),
                    Paragraph(Text("The finite-box identity is the one-dimensional scaled version of the derivative/difference relation in Michele Vergne, A remark on the convolution with the box spline, Annals of Mathematics 174 (2011), 607-618, Section 1, immediately before Section 2; DOI 10.4007/annals.2011.174.1.19. This integration is repo-derived and is not claimed as a new interpolation theorem. Source remains Candidate pending actual Lean compilation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rational-even-interpolation-jet-budget"),
                DeclarationHandle.Create(Prefix + "rationalInterpolationJetBudget"), H("Executable rational constants"),
                StatementSource.FromAuthor(Disp(F.Id("The same formula J_s is implemented over rational numbers using natural powers and field operations."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rational function computes a budget, not the transcendental interpolating function itself. Validity requires nonnegative R,V and positive sigma with certified nodal bounds. Division by a zero uncertified gap is not an admissible application."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-even-jet-real-semantics"),
                DeclarationHandle.Create(Prefix + "rationalInterpolationJetBudget_cast"), H("Exact rational-to-real semantics"),
                StatementSource.FromAuthor(Disp(F.Id("Casting rationalInterpolationJetBudget into the reals gives interpolationJetBudget exactly."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality is proved by the field-cast identities. Thus rational arithmetic can supply the finite J0,J2 inputs of RationalWeilJetBudget without numerical differentiation or uncomputed derivative seminorms."))), DescribeRole.Theorem)), []));
}
