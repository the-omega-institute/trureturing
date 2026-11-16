using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceGermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "OriginalGaussianSourceGerm", H("Original source contraction germs and trace similarity"), Blocks(
            Paragraph(Text("For a fixed frequency cutoff, both actual internal source matrices vanish at zero. The right matrix contains every retained colour in its original inverse substitution. Entrywise positive comparisons vanish there as well. Finite dimensional continuity gives one positive closed contraction disk for these four matrices. Its radius may depend on the cutoff; the resulting occupation majorant is fixed only at this cutoff, and no convergence on the unit disk is asserted.")),
            Paragraph(Text("The raw product is diagonally similar to the colour identity tensored with the square of the normalized finite section. Cyclicity of trace removes the positive frequency diagonal at every power, including power zero. Thus the arbitrary-mean finite sewing trace exponential is exactly exp(-(rank/2)*finiteLog). This algebraic identity needs no inverse of the sewing variable and includes empty mode or colour types. The native coefficient comparison proves a summable majorant uniformly over the closed source germ and both external unit polydisks. It controls the actual mixed means and exponentials. Exact diagonal scaling retains twice the internal occupation energy. Finite arbitrary-mean sewing holds before external extraction. The source energy layer stabilizes by full-colour box restriction; external analytic coefficient extraction remains separate.")),
            Describe.Lean(DescribeId.Create("original-source-positive-internal"),
                DeclarationHandle.Create(Prefix + "positiveInternal"), H("Positive internal comparison"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take each undamped internal entry's norm and multiply by the two nonnegative radius powers at its positive frequencies. The complete inverse colour transport precedes this comparison."))), DescribeRole.Definition),
            N("left_entry_differentiable", "Polynomial left entries", "Every actual damped left entry is a polynomial in the source variable."),
            N("right_entry_differentiable", "Polynomial fully transported right entries", "The inverse transport is independent of the source variable, and damping makes each actual right entry a polynomial."),
            N("original_rows_contract_on_germ", "A common fixed-cutoff contraction germ", "A finite intersection of strict norm neighbourhoods contains a positive closed disk. Both raw internal matrices and both positive comparisons are strict Euclidean contractions throughout it. No positive-rank or nonempty-support assumption occurs."),
            N("original_rows_trace_power", "Literal raw trace similarity", "At every nonnegative power p the raw internal product trace is rank times trace(finiteSection to the power 2*p). The proof retains the complete inverse Gram transport and both positive frequency diagonals."),
            N("original_rows_trace_prefactor", "Exact finite sewing normalization", "The trace-power identity and scalar linearity of the trace series give exp(-(rank/2)*finiteLog). No charge average or extra overall factor is introduced."),
            D("mixedMean", "Actual mixed mean", "The original internal mean plus the finite original internal-to-external couplings evaluated at the retained external coordinates."),
            D("externalExponent", "Original external exponent", "One half of the ordinary external quadratic sum plus the original external linear sum, without conjugation."),
            D("originalMean", "Undamped original mean", "The original corrected mean is restricted to the full internal colour-frequency box and the given external labels."),
            D("originalInverseMean", "Fully transported opposite-charge mean", "Apply the complete inverse colour substitution to the original mean at charge minus a before any frequency restriction."),
            D("occupationTerm", "Literal mixed occupation term", "The two actual affine coefficients are multiplied by one internal factorial and both original external exponentials."),
            D("sourcePolydisk", "Fixed-cutoff source domain", "A closed source disk times the two external unit polydisks, including empty external families."),
            N("rightMean_raw", "Literal raw right mean", "The actual damped opposite-charge mean is the damping times its complete original inverse-colour transport. This interface is consumed by the nested-box coefficient restriction proof."),
            N("original_occupation_majorant_on_germ", "Uniform summable occupation majorant", "Coefficientwise finite polynomial comparison dominates the actual covariances and mixed means by symmetric nonnegative arrays at one fixed radius. The accepted affine factorial-square summability supplies a single summable bound independent of the source and external points."),
            N("original_occupation_normal_on_germ", "Normal convergence before extraction", "The summable majorant yields uniform convergence of all finite occupation partial sums on the closed fixed-cutoff source polydisk."),
            D("internalEnergy", "Positive internal energy", "Sum frequency times occupation over the full internal support, with positive frequencies starting at one."),
            N("original_row_coefficients_scale", "Exact full-row energy scaling", "Both literal affine row coefficients scale by the source power at their internal energy. Each full native row degree retains its external occupation."),
            N("original_row_product_scales", "Twice the internal energy", "The product has exactly one internal factorial and exactly the source power twice its internal energy, also at zero energy."),
            D("rawOccupationTerm", "Undamped mixed source expression", "The algebraic expression retains both original means, the transported right covariance and both external coordinate families; no summability at source value one is asserted."),
            N("original_occupation_scales", "Mixed-source energy scaling", "The actual mixed mean scales with its internal frequency, while the external exponent stays fixed. Diagonal Gaussian congruence gives exactly twice the occupation energy."),
            D("finiteMixedExponent", "Uncollected finite sewn exponent", "Both original external exponents plus the ordered effective quadratic expression in the two actual mixed means."),
            N("original_rows_symm", "Actual row symmetry", "Both actual damped covariances are symmetric under ordinary transpose. Complete inverse transport preserves the original covariance symmetry before damping."),
            N("original_occupation_sewing_on_germ", "Literal finite mixed-mean sewing", "One common fixed-cutoff germ supports normal convergence and the exact arbitrary-mean sewing equality. Its determinant factor is exp(-(rank/2)*finiteLog), with no inverse of the source variable.")), []));

    private static DocumentBlock D(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-source-germ-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("original-source-germ-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
