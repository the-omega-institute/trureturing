using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mehat;

internal sealed class OrthogonalityProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Mehat/OrthogonalityProducts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/mehat2026eulermagic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrarily many integer orthogonality factors can have pairwise distinct products of entry squares.",
        H("Integer orthogonality factors and square-product separation"),
        Blocks(
            Describe.Lean(DescribeId.Create("mehat-problem92-statement"),
                DeclarationHandle.Create(Prefix + "Problem92"), H("Problem 9.2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive natural k there are k integer matrices of order three, each with a nonzero integer constant gamma and A times its transpose equal to gamma times the identity. The map from all functions choosing one of the nine entry positions in each factor to the product of those entry squares is injective. The matrices and constants may depend on k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mehat-problem91-statement"),
                DeclarationHandle.Create(Prefix + "Problem91"), H("Problem 9.1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural k at least two there is an integer matrix M of order three to the power k, with nonzero integer constant gamma, satisfying orthogonality, both squared diagonal sums equal to gamma, and injectivity of entry squares over all positions. The second diagonal uses the usual reversed finite index. This statement is separate from the factor theorem."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mehat-quaternion-matrix"),
                DeclarationHandle.Create(Prefix + "quaternionMatrix"), H("Quaternion factors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The classical quaternion rotation formula gives a polynomial matrix with orthogonality constant equal to the square of the sum of the four coordinate squares. Individual factors need not satisfy either Euler diagonal equation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mehat-problem92-factor-existence"),
                DeclarationHandle.Create(Prefix + "problem92"), H("Factors for every positive length"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any two different coordinate polynomials, an integer quaternion makes the first zero and the second nonzero. Thus no nonzero weighted difference of their squares vanishes identically. For equal coordinates, different nonzero old products also give a nonzero difference. The product of all collision polynomials and all entry polynomials is nonzero in the integer polynomial ring. MvPolynomial.funext implies that it is nonzero at some integer tuple. Appending this quaternion factor preserves nonzero entries and injectivity, so induction gives every finite length. The induction includes the empty tuple only as an auxiliary extension; Problem 9.2 asserts positive lengths. No coefficient-size bound, efficient construction, order-seven result, or full Euler-matrix theorem is asserted here."))),
                DescribeRole.Theorem)),
        []));
}
