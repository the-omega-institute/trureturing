using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class EulerProductDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/EulerProduct",
            "Finite Euler windows and single-address weights connect the prime and zero sides."),
        H("Euler Windows and Single-Address Heat"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("finite-euler-windows-have-only-the-local-lattice"),
                DescribeKind.Theorem,
                H("Finite Euler windows have only the local denominator lattice"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus")),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("single-address-reading-is-the-von-mangoldt-weight"),
                DescribeKind.Definition,
                H("The single-address reading is the von Mangoldt weight"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/EulerProduct.single_address_reading_spec")),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("the-logarithmic-derivative-is-the-single-address-heat-trace"),
                DescribeKind.Proposition,
                H("The logarithmic derivative is the single-address heat trace"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative")),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane.")))))));
}
