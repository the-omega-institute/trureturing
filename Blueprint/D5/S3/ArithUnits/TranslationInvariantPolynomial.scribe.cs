using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class TranslationInvariantPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/TranslationInvariantPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The additive orbit polynomial generates the algebra of translation invariants.",
        H("Translation-Invariant Polynomials"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-comp-of-translation-invariant"),
                DeclarationHandle.Create(Prefix + "exists_comp_of_translation_invariant"),
                H("A generator for nonzero translation invariants"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be any prime and K any field of characteristic p. For every "
                            + "nonzero a in K, every polynomial fixed by substitution T + a is "
                            + "a polynomial over the same field in T^p - a^(p-1) T. The field "
                            + "need not be finite or algebraically closed, and the polynomial "
                            + "may be zero or constant.")),
                    Paragraph(Text(
                        "The generator is fixed by translation. Euclidean division by this "
                            + "monic polynomial preserves translation invariance of both the "
                            + "quotient and remainder, by uniqueness of division. The remainder "
                            + "has degree below p. Its values at the p distinct prime-field "
                            + "multiples of a agree, so interpolation makes it constant. "
                            + "Induction on degree then constructs the composition polynomial.")),
                    Paragraph(Text(
                        "For a finite set S with S + a = S, its actual root polynomial, the "
                            + "product of T - x over x in S, is fixed by this substitution: "
                            + "translation by -a permutes the factors. It therefore has the "
                            + "same-field representation above. Empty S is included; its root "
                            + "polynomial is 1. This argument uses polynomial division and "
                            + "distinct roots rather than reversing Newton identities."))),
                DescribeRole.Theorem))));
}
