using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class TwoBasicOpenCechExactDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/HomologicalAlgebra/TwoBasicOpenCechExact.";

    private static readonly LibraryNoteRef StacksSource =
        LibraryNoteRef.Create(
            "D5/L/HomologicalAlgebra/stacksproject2026twobasicopencech");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The degree-zero Cech complex of two principal opens covering an affine scheme "
            + "is a short exact complex of modules.",
        H("The Two-Basic-Open Cech Complex"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-basic-open-cech-complex"),
                DeclarationHandle.Create(Prefix + "twoBasicOpenCechComplex"),
                H("The concrete localization complex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(StacksSource),
                Blocks(Paragraph(Text(
                    "For a commutative ring R and elements f and g, the complex maps R "
                        + "diagonally to Away f times Away g. Its second map sends (x, y) "
                        + "to the image of x under awayToAwayRight minus the image of y "
                        + "under awayToAwayLeft in Away (f g)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-basic-open-cech-short-exact"),
                DeclarationHandle.Create(Prefix + "two_basic_open_cech_short_exact"),
                H("Short exactness under the covering condition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(StacksSource),
                Blocks(
                    Paragraph(Text(
                        "If f and g generate the unit ideal, the diagonal is injective and "
                            + "its image is the kernel of the overlap difference. The kernel "
                            + "argument uses the unique gluing theorem for localizations.")),
                    Paragraph(Text(
                        "Surjectivity remains constructive. An overlap fraction with "
                            + "denominator (f g)^n is split using coefficients u and v with "
                            + "u f^n + v g^n = 1; the fractions (a v)/f^n and "
                            + "-(a u)/g^n form a preimage pair under the overlap-difference map.")),
                    Paragraph(Text(
                        "Stacks tags 00EK and 01X9 supply the classical localization and "
                            + "affine-Cech mathematics. The exact ModuleCat object, chosen "
                            + "map orientation, and explicit powered-denominator proof are "
                            + "the repository's concrete Lean realization."))),
                DescribeRole.Theorem))));
}
