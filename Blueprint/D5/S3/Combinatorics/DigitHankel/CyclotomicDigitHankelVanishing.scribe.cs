using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DigitHankel;

internal sealed class CyclotomicDigitHankelVanishingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelVanishing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/sobolewski2026hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse Kernels at Cyclotomic Parameters",
        H("Sparse Kernels at Cyclotomic Parameters"),
        Blocks(
            Node("cyclotomic-digit-hankel-vanishing-sparse", "Sparse kernel interval criterion", "sparse_kernel_interval", "If two finitely supported coefficient sequences have the stated support, nonzero witnesses, zero total sum, and both digit-sum convolution identities, then the Hankel determinant at the indicated size and parameter t is zero.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-vanishing-odd", "Odd carry kernel", "odd_carry_kernel", "For a field of characteristic zero, if f changes by one between every even and following odd index, then every positive odd size has a nonzero vector in the kernel of the corresponding carry-difference matrix.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-vanishing-base", "Root base kernel", "root_base_kernel", "For positive d and k and a parameter zeta with zeta to the d equal to one, there is a coefficient sequence beginning with one, vanishing on the final prescribed interval, summing to zero, and annihilating the digit-sum Hankel rows together with the odd carry rows.", DescribeRole.Theorem),
            Node("cyclotomic-digit-hankel-vanishing-second", "Root second kernel", "root_second_kernel", "For positive d and a parameter zeta with zeta to the d equal to one, there is a coefficient sequence beginning with one, vanishing on the final interval of length 2 to the d minus one, summing to zero, and annihilating every digit-sum Hankel row through size 2 to the 2d.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
