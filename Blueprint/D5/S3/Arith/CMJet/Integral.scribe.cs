using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CMJet;

internal sealed class CMJetIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CMJet/Integral.";

    private static readonly LibraryNoteRef Alpoge =
        LibraryNoteRef.Create("D5/L/Zeros/alpoge2026riemann");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The p-fold derivative at an inert prime is p times an integral linear endomorphism. "
            + "Repeated blocks give an integral factorization of all jets and a divisor of the "
            + "content of the complete row.",
        H("The integral inert operator and the complete jet row"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reduce-iter"),
                DeclarationHandle.Create(Prefix + "reduce_iter"),
                H("Coefficient reduction respects iteration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reducing both components modulo p commutes with the derivation, hence with each "
                        + "iterate of every order."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("inertlift"),
                DeclarationHandle.Create(Prefix + "inertLift"),
                H("The integral quotient endomorphism"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p ≡ 3 modulo 4, the pointwise quotient of D^p by p exists by reduction and "
                        + "is unique by torsion-freeness of the integral polynomial pairs. Uniqueness gives "
                        + "linearity over the integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("iter-eq-inertlift"),
                DeclarationHandle.Create(Prefix + "iter_eq_inertLift"),
                H("Exact integral factorization of iterates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write N = p q + r with q = N div p and r = N mod p. On every integral pair, D^N acts "
                        + "as p^q times q applications of the integral quotient to D^r of the input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inert-dvd-jet"),
                DeclarationHandle.Create(Prefix + "inert_dvd_jet"),
                H("Divisibility of every evaluated jet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Alpoge),
                Blocks(Paragraph(Text(
                    "For each inert prime p and every natural order N, the evaluated derivative of every "
                        + "integral polynomial pair at the base point is divisible by p^(N div p)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row"),
                DeclarationHandle.Create(Prefix + "row"),
                H("The complete row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At order N = 4m+1, the row reads the jets of X^(4j+1) for 0 ≤ j ≤ m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("jet-monomial-outside-row"),
                DeclarationHandle.Create(Prefix + "jet_monomial_outside_row"),
                H("Vanishing outside the row"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A pure monomial of exponent greater than N or outside the class one modulo four has "
                        + "zero evaluated jet at order N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row-last"),
                DeclarationHandle.Create(Prefix + "row_last"),
                H("The last column is N!"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The final exponent is N, so the factorial highest-monomial rule gives N! for the last "
                        + "entry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inert-dvd-content"),
                DeclarationHandle.Create(Prefix + "inert_dvd_content"),
                H("An inert prime power divides the row content"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every entry is divisible by p^(N div p), hence so is the gcd of their absolute values. "
                        + "The nonzero last entry also ensures positive content dividing N!."))),
                DescribeRole.Theorem)
        )));
}
