using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class LucasSquareClassificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic Lucas moduli classify every square and twice-square Lucas value.",
        H("Lucas Squares and Twice Squares"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-square-classifications"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/LucasSquareClassification.lucas_square_classifications"),
                H("Complete classifications, including index zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural index n, the integer Lucas number L_n is a square "
                            + "exactly when n is one or three. It equals twice an integer square "
                            + "exactly when n is zero or six. The exceptional values are "
                            + "L_0 = 2, L_1 = 1, L_3 = 4 and L_6 = 18.")),
                    Paragraph(Text(
                        "The proof follows Cohn's classical classifications in Square Fibonacci "
                            + "Numbers, Etc., Theorems 1 and 2. Finite reductions modulo four "
                            + "exclude all even indices from the square case; reductions modulo "
                            + "eight exclude all odd indices from the twice-square case. "
                            + "The remaining indices use a modulus L_(2^(r+1)), which is "
                            + "three modulo four.")),
                    Paragraph(Text(
                        "Trace and norm in the golden integer ring give an antiperiod "
                            + "of the golden unit modulo that Lucas number. An odd multiple "
                            + "of the antiperiod makes the required residues minus one, "
                            + "minus four, or minus thirty-six. In the last case, the modulus "
                            + "is also coprime to three. Their Jacobi symbols are minus one. "
                            + "The residue obtained through the negative index minus six "
                            + "is derived by multiplying by the conjugate of the sixth power.")),
                    Paragraph(Text(
                        "These are the classical one-index Lucas classifications used "
                            + "by the Fibonacci square-class argument. General product "
                            + "exclusions for distinct Fibonacci or Lucas indices require "
                            + "their separate proofs."))),
                DescribeRole.Theorem))));
}
