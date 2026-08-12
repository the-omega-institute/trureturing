using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class EulerProductDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite Euler windows and single-address weights connect the prime and zero sides.", H("Euler Windows and Single-Address Heat"), Blocks(
            Describe.Lean(DescribeId.Create("finite-euler-windows-have-only-the-local-lattice"), DeclarationHandle.Create("D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus"), H("Finite Euler windows have only the local denominator lattice"), StatementSource.FromAuthor(FiniteEulerStatement()), AssessedProvenance.FromLiterature(Apostol), Blocks(Paragraph(Text(
                    "A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-address-reading-is-the-von-mangoldt-weight"), DeclarationHandle.Create("D5/S3/Weil/EulerProduct.single_address_reading_spec"), H("The single-address reading is the von Mangoldt weight"), StatementSource.FromAuthor(SingleAddressReadingStatement()), AssessedProvenance.FromLiterature(Apostol), Blocks(Paragraph(Text(
                    "Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("the-logarithmic-derivative-is-the-single-address-heat-trace"), DeclarationHandle.Create("D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative"), H("The logarithmic derivative is the single-address heat trace"), StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, D(1), Lt, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("singleAddressHeatTrace")), Open, F.Id("s"), Close, Eq, Minus, Frac, Grp(Operatorname, Grp(F.Id("deriv")), Open, Operatorname, Grp(F.Id("classicalZeta")), Close, Open, F.Id("s"), Close), Grp(Operatorname, Grp(F.Id("classicalZeta")), Open, F.Id("s"), Close)))), AssessedProvenance.FromLiterature(Apostol), Blocks(Paragraph(Text(
                    "In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane."))), DescribeRole.Proposition),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("journal-and-ledger-readings"),
                H("Journal and ledger readings"),
                DescribeStatement.FromLean(LeanTheorem("D5/S3/Weil/EulerProduct.single_address_reading_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Ordering terms by generated value resembles a chronological journal, while grouping powers by prime address resembles a classified ledger. The single-address theorem supplies the local weight behind that analogy; it does not formalize heat-time cosmology or a theta functional equation.")))),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("finite-euler-windows-do-not-create-global-zeros"),
                H("Finite Euler windows do not create global zeros"),
                DescribeStatement.FromLean(LeanTheorem("D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Every regular finite Euler window is nonzero, so no finite set of local factors realizes a nontrivial global zero. This supports only a finite-versus-tail boundary; collective-mode, prime-deletion, dense-phase, and equal-loudness interpretations are not proved here.")))))));

    private static Formula FiniteEulerStatement() => Disp(Seq(Forall, Sp, F.Id("S"), Subset, Underscore, Grp(Operatorname, Grp(F.Id("fin"))), Mathbb, Grp(F.Id("N")), Comma, Esc, Open, Forall, Sp, F.Id("p"), InMacro, Sp, F.Id("S"), Comma, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, Operatorname, Grp(F.Id("finiteEulerProduct")), Open, F.Id("S"), Comma, F.Id("s"), Close, Neq, Sp, D(0), Sp, Leftrightarrow, Sp, Operatorname, Grp(F.Id("FiniteEulerRegular")), Open, F.Id("S"), Comma, F.Id("s"), Close, Close, Sp, Land, Sp, Open, Neg, Operatorname, Grp(F.Id("FiniteEulerRegular")), Open, F.Id("S"), Comma, F.Id("s"), Close, Sp, Leftrightarrow, Sp, Exists, Sp, F.Id("p"), InMacro, Sp, F.Id("S"), Comma, Exists, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc, F.Id("s"), Eq, Frac, Grp(D(2), Pi, Sp, F.Id("i"), Sp, F.Id("k")), Grp(Log, Sp, F.Id("p")), Close));

    private static Formula SingleAddressReadingStatement() => In(Seq(
        Open, Forall, Sp, F.Id("p"), Comma, Sp, F.Id("k"), Comma, Esc,
        Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp,
        F.Id("k"), Neq, D(0), Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("singleAddressReading")),
        Open, F.Id("p"), Caret, F.Id("k"), Close, Eq,
        Log, Sp, F.Id("p"), Close, Sp, Land, Sp,
        Open, Forall, Sp, F.Id("n"), Comma, Esc,
        Neg, Operatorname, Grp(F.Id("IsPrimePow")), Open, F.Id("n"), Close,
        Sp, Rightarrow, Sp,
        Operatorname, Grp(F.Id("singleAddressReading")), Open, F.Id("n"), Close,
        Eq, D(0), Close));
}
