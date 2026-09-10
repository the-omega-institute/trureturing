using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilEvenDualStencilDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilEvenDualStencil.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual even zero-trace Fourier stencil has an explicit arithmetic column and a complete inverse-square envelope for certified energy-dual trials.",
        H("Even Arithmetic Dual Stencil"),
        Blocks(
            Describe.Lean(DescribeId.Create("arithmetic-boundary-symbol-neg"),
                DeclarationHandle.Create(Owner + "arithmetic_boundary_symbol_neg"),
                H("Reflection of the original arithmetic symbol"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual arithmeticBoundarySymbol is odd in its integer frequency. The proof unfolds the original finite prime, pole and infinite Gamma expression through a private definitional presentation. No zero data, symmetry premise or replacement public symbol is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("arithmetic-boundary-symbol-zero"),
                DeclarationHandle.Create(Owner + "arithmetic_boundary_symbol_zero"),
                H("Central arithmetic symbol"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Oddness implies the existing symbol vanishes at zero. This companion is used when evaluating the central coefficient of the stencil."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-trace-column"),
                DeclarationHandle.Create(Owner + "zeroTraceColumn"),
                H("Original column of the specified Fourier stencil"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing couplingColumn with support {n,-n,0}, coefficient -2 at zero and 1 at the two other frequencies. For n positive this represents V_n+V_(-n)-2V_0, with zero endpoint trace. The arithmetic action is specified before evaluating it."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-trace-column-formula"),
                DeclarationHandle.Create(Owner + "zero_trace_column_formula"),
                H("Exact arithmetic cancellation on the three-point stencil"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive integer n and exterior integer m with |m|>n, the canonical column equals 2n*(m*s_n-n*s_m)/(pi*m*(m^2-n^2)). The proof expands the original finite column, uses proved arithmetic oddness and checks all denominators before cancellation. Both signs of m remain covered."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-trace-column-bound"),
                DeclarationHandle.Create(Owner + "zero_trace_column_bound"),
                H("Actual inverse-square exterior estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For c>=2, n>0 and |m|>=2n, use the previously proved prime-pole-Gamma envelope B_c to obtain norm(column)<=4*B_c*n/(pi*|m|^2). The factorization of m^2-n^2 preserves cancellation and improves the generic separate-coefficient estimate. There is no terminal exterior cutoff or assumed moment condition."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-zero-trace-columns-bound"),
                DeclarationHandle.Create(Owner + "finite_zero_trace_columns_bound"),
                H("Finite complex trial with a complete arithmetic tail constant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any finite positive-index set and complex stencil coefficients t_n, bound the actual summed exterior column by 4*B_c/(pi*|m|^2) times sum n*norm(t_n). The concrete consumer reconstructs two exact Gaussian-rational pivots, proves endpoint and candidate-pairing equalities by exact arithmetic, and encloses all retained and exterior residual modes before using the existing energy-dual variational theorem.")),
                    Paragraph(Text("The physical Fourier/operator-domain identification, historical full-space coercivity, infinite fourth-power sum, complex-disk extension and interval verifier remain separately stated paper/computer-assisted bridges. No optimal trial or all-scale convergence is assumed. Lean elaboration, Scribe emission and a transitive axiom report have not been run."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet"))]));
}
