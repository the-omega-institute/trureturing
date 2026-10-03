using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.NumberFieldZeta;

internal sealed class NumberFieldEulerProductDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-ideal Euler product.",
        H("Prime-ideal Euler product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-ideal"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.NonzeroIdeal"),
                H("Nonzero Integral Ideals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The subtype of integral ideals of the ring of integers of L that are not the zero " +
                    "ideal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ideal-norm-multiplicity"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.idealNormMultiplicity"),
                H("Ideal Norm Multiplicity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a natural number n, the number of nonzero integral ideals whose absolute norm " +
                    "equals n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dedekind-zeta-eq-tprod-prime-ideal"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal"),
                H("Prime-ideal Euler product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Prime-ideal Euler product (Sharifi, *Algebraic Number Theory*, Theorem 7.1.12, p. " +
                    "140): for 1 < Re s, ζ_L(s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1} over the nonzero prime ideals of 𝓞 L."))),
                DescribeRole.Theorem)
        )));
}
