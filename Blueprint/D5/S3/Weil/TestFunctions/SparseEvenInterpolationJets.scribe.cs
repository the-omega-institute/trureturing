using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class SparseEvenInterpolationJetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/SparseEvenInterpolationJets.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual smooth sparse interpolation with explicit finite jet budgets and repeated exceptional nodes.",
        H("Sparse Even Interpolation and Quantitative Jets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-even-squaredExceptionPolynomial"),
                DeclarationHandle.Create(Prefix + "squaredExceptionPolynomial"),
                H("Indexed exceptional annihilator"),
                StatementSource.FromAuthor(Disp(F.Id("A(X)=product_n(X-w_n^2)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The indexing type is finite. The node map may repeat values; no injectivity assumption is present."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseEvenPolynomial"),
                DeclarationHandle.Create(Prefix + "sparseEvenPolynomial"),
                H("Target-only normalized solve"),
                StatementSource.FromAuthor(Disp(F.Id("P=A times Lagrange(targets, values/(A(target)*seed))."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The denominator is evaluated only at targets. Exceptional-to-exceptional distances never occur."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseCoefficientBudget"),
                DeclarationHandle.Create(Prefix + "sparseCoefficientBudget"),
                H("Finite coefficient budget"),
                StatementSource.FromAuthor(Disp(F.Id("M=(1+Y^2)^e * interpolationCoefficientBudget(d,R,sigma,V/tau^e)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("R bounds targets, Y bounds exceptions, sigma separates distinct squared targets, and tau separates each squared target from each squared exception."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseJetBudget"),
                DeclarationHandle.Create(Prefix + "sparseJetBudget"),
                H("Explicit derivative budget"),
                StatementSource.FromAuthor(Disp(F.Id("J_s=(d+e+1) M [8(2(d+e)+3)(R+1)]^(2(d+e)+s)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative order includes the annihilator degree. Removing unnecessary gap assumptions does not remove the cost of enforcing exceptional zeros."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-even-squaredExceptionPolynomial-zero"),
                DeclarationHandle.Create(Prefix + "squaredExceptionPolynomial_zero"),
                H("Repeated exceptions are annihilated"),
                StatementSource.FromAuthor(Disp(F.Id("A(w_n^2)=0 for every exception index n."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One factor in the finite product vanishes. Repeated exception values are permitted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-squaredExceptionPolynomial-lower"),
                DeclarationHandle.Create(Prefix + "squaredExceptionPolynomial_lower"),
                H("Target denominator lower bound"),
                StatementSource.FromAuthor(Disp(F.Id("If tau>0 and tau<=|u-w_n^2| for every n, then tau^e<=|A(u)|."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the certified nonnegative factor lower bounds. No separation between two exceptions is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-squaredExceptionPolynomial-unit-disk"),
                DeclarationHandle.Create(Prefix + "squaredExceptionPolynomial_unit_disk"),
                H("Annihilator disk bound"),
                StatementSource.FromAuthor(Disp(F.Id("If |w_n|<=Y and Y>=0, then |A(u)|<=(1+Y^2)^e for |u|<=1."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the triangle inequality to each factor and multiply. This is an estimate for the actual exception polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseEvenPolynomial-target-value"),
                DeclarationHandle.Create(Prefix + "sparseEvenPolynomial_target_value"),
                H("Exact target interpolation"),
                StatementSource.FromAuthor(Disp(F.Id("If squared targets are injective and seed_i*A(z_i^2) is nonzero, then P(z_i^2)*seed_i=values_i."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing Mathlib Lagrange theorem returns the normalized target value; cancellation restores the prescribed value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseEvenPolynomial-exception-value"),
                DeclarationHandle.Create(Prefix + "sparseEvenPolynomial_exception_value"),
                H("Exact exceptional zeros"),
                StatementSource.FromAuthor(Disp(F.Id("P(w_n^2)=0 for every exception n."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The annihilator remains a factor of the final polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseEvenPolynomial-coeff-bound"),
                DeclarationHandle.Create(Prefix + "sparseEvenPolynomial_coeff_bound"),
                H("Gautschi-type sparse coefficient control"),
                StatementSource.FromAuthor(Disp(F.Id("For certified radii R,Y, gaps sigma,tau>0, amplitude V>=0 and seed floor 1/2, every coefficient of P has norm at most M."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing Lagrange disk product bound, the exception denominator lower bound and the unit-disk coefficient theorem. Gautschi (1962), Section 2 (2.1), and Section 3, Theorem 1 (3.1), supply the classical product mechanism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-sparseEvenPolynomial-natDegree-le"),
                DeclarationHandle.Create(Prefix + "sparseEvenPolynomial_natDegree_le"),
                H("Count the exceptional derivative cost"),
                StatementSource.FromAuthor(Disp(F.Id("natDegree(P)<=d+e."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product degree is bounded by the sum of the exception count and the target interpolation degree. Zero target data and empty types are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-exists-sparse-even-interpolant-with-explicit-jets"),
                DeclarationHandle.Create(Prefix + "exists_sparse_even_interpolant_with_explicit_jets"),
                H("Actual smooth sparse interpolation"),
                StatementSource.FromAuthor(Disp(F.Id("Under the finite geometric certificates, there exists an even smooth compact test g with FT(g)(z_i)=values_i, FT(g)(w_n)=0, support in [-h,h], and L1(D^s g)<=J_s for s<=2; h=1/(4(R+1))."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Construct the actual finite-box seed using q=2(d+e)+2 averages and apply the existing polynomial differential realization. The finiteBoxSeed budget proves all needed derivative estimates without any unknown bump seminorm. Vergne (2011), Section 1, records the classical box-spline derivative/finite-difference identity used by that owner. The result imposes no mutual exceptional separation. It assumes certified target and target-exception geometry and does not assert any off-line zeta zero exists."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-even-rationalSparseJetBudget"),
                DeclarationHandle.Create(Prefix + "rationalSparseJetBudget"),
                H("Rational execution"),
                StatementSource.FromAuthor(Disp(F.Id("Evaluate J_s using rational R,Y,sigma,tau,V and natural counts."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The arithmetic is total. Its use as a bound requires the signs and actual geometric inequalities in the semantic theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-even-rationalSparseJetBudget-cast"),
                DeclarationHandle.Create(Prefix + "rationalSparseJetBudget_cast"),
                H("Exact real semantics of rational arithmetic"),
                StatementSource.FromAuthor(Disp(F.Id("The rational budget cast to the reals equals sparseJetBudget."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof uses only rational cast homomorphisms. No floating-point rounding or external numerical oracle enters."))),
                DescribeRole.Theorem)), []));
}
