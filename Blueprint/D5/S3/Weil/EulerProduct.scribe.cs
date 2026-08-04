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
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("finite-euler-windows-have-only-the-local-lattice"),
                H("Finite Euler windows have only the local denominator lattice"),
                LeanTheorem(
                    "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexMacro(FormulaLatexMacro.Subset), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("fin"))])]), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Prime"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("finiteEulerProduct"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Neq), new Formula.LatexSpace(), new Formula.LatexDigits([0]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("FiniteEulerRegular"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Neg), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("FiniteEulerRegular"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Exists), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Exists), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([2]), new Formula.LatexMacro(FormulaLatexMacro.Pi), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("i")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("k"))]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Log), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("p"))]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "A finite Euler product is nonzero exactly on the locus where every local denominator is nonzero, and the complementary denominator-zero locus is the union of the imaginary lattices indexed by its primes. Lean totalizes inversion with zero inverse equal to zero, so the zero-free clause is deliberately restricted to the regular locus; no pole order or numerical window certificate is asserted.")))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("single-address-reading-is-the-von-mangoldt-weight"),
                H("The single-address reading is the von Mangoldt weight"),
                LeanTheorem(
                    "D5/S3/Weil/EulerProduct.single_address_reading_spec"),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "Under the value map from a one-prime ledger state to a natural prime power, a nonzero exponent at p reads log p, while every non-prime-power value reads zero. This is the classical von Mangoldt coefficient in the repository's single-address coordinates.")))
            ),
            DocumentBlock.Describe.Proposition(
                DescribeId.Create("the-logarithmic-derivative-is-the-single-address-heat-trace"),
                H("The logarithmic derivative is the single-address heat trace"),
                LeanTheorem(
                    "D5/S3/Weil/EulerProduct.single_address_heat_trace_eq_log_derivative"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexMacro(FormulaLatexMacro.Re), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("singleAddressHeatTrace"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("deriv"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("classicalZeta"))]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("classicalZeta"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])])),
                DescribeProvenance.LiteratureAttested(Apostol),
                Blocks(Paragraph(Text(
                    "In the convergence half-plane with real part greater than one, the L-series of the single-address reading equals minus the derivative of the classical zeta function divided by the zeta function. The statement adds no continuation beyond that half-plane.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("journal-and-ledger-readings"),
                H("Journal and ledger readings"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/EulerProduct.single_address_reading_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Ordering terms by generated value resembles a chronological journal, while grouping powers by prime address resembles a classified ledger. The single-address theorem supplies the local weight behind that analogy; it does not formalize heat-time cosmology or a theta functional equation.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("finite-euler-windows-do-not-create-global-zeros"),
                H("Finite Euler windows do not create global zeros"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/EulerProduct.finite_euler_zero_free_and_pole_locus")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Every regular finite Euler window is nonzero, so no finite set of local factors realizes a nontrivial global zero. This supports only a finite-versus-tail boundary; collective-mode, prime-deletion, dense-phase, and equal-loudness interpretations are not proved here.")))
            ))));
}
