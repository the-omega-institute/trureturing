using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class EuclideanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/Euclidean",
            "Nearest-coordinate division makes the golden integers norm-Euclidean."),
        H("Golden Euclidean Division"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("norm-euclidean-division"),
                DescribeKind.Theorem,
                H("Norm-Euclidean division"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S0/Carrier/Euclidean.golden_division")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/Carrier/chatland1949euclidean")),
                Blocks(
                    Paragraph(Text(
                        "For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.")),
                    Paragraph(Text(
                        "If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.")),
                    Paragraph(Text(
                        "The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`."))),
                LatexStatement.Create(@"$$\forall a,b\in\mathbb{Z}[\varphi],\ b\neq 0 \Rightarrow \exists q,r\in\mathbb{Z}[\varphi],\ a=qb+r \land (r=0 \lor \lvert\operatorname{norm}(r)\rvert<\lvert\operatorname{norm}(b)\rvert)$$")))));
}
