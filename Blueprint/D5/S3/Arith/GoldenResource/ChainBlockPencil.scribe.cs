using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class ChainBlockPencilDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/ChainBlockPencil.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit endpoint couplings preserve positive lower bounds independent of chain length.",
        H("Chain Block Pencil"),
        Blocks(
            Paragraph(Text("Let n be any natural number and put m=n+1. Each hidden chain "
                + "has m vertices and matrix H(m), with diagonal four and adjacent entries "
                + "minus one. The hidden space is the direct sum of two identical chains, "
                + "ordered first chain then second chain. Two visible coordinates precede "
                + "the hidden coordinates. B has first row the first unit vector of the "
                + "first chain and second row the first unit vector of the second chain. "
                + "K(n) has blocks I, B, B transpose, and H(m) direct sum H(m). "
                + "For real k and b, G(n,k,b) is diagonal: every diagonal entry is k except "
                + "the last vertex of the first hidden chain, whose entry is k-b. "
                + "Write V(x) for the sum of coordinate squares and Q(A,x) for x transpose A x. "
                + "PosSemidef and PosDef denote positive semidefiniteness and positive "
                + "definiteness. Every statement involving G assumes k at least two and "
                + "b at most one; in particular it applies to both b=0 and b=1. "
                + "For the coefficient and combined statements, k and b are integers, "
                + "and b is also nonnegative. Coeff(n,k,b,i,j) means there exist integers "
                + "a and c equal to the corresponding entries K(n)(i,j) and G(n,k,b)(i,j), "
                + "with both absolute values at most max(k,4). Uniform(n,k,b) means "
                + "K(n) minus one third of the identity is positive semidefinite, "
                + "G(n,k,b) minus the identity is positive semidefinite, and "
                + "Coeff(n,k,b,i,j) holds for every pair of coordinates i and j.")),
            Describe.Lean(
                DescribeId.Create("mass-uniform-energy-bound"),
                DeclarationHandle.Create(Prefix + "mass_coercive"),
                H("Uniform mass energy"),
                StatementSource.FromAuthor(Disp(Le(
                    Seq(Third(), Cdot, Sp, Call("V", F.Id("x"))),
                    Call("Q", Mass(), F.Id("x"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each visible scalar a and its chain h, "
                    + "(2a+3h(0)) squared is nonnegative. Thus the cross term is bounded below "
                    + "by minus two thirds of a squared minus three halves of h(0) squared. "
                    + "The first coordinate square is at most the sum of all chain squares. "
                    + "The chain energy is at least twice that sum. Adding the two chains "
                    + "gives the uniform factor one third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mass-loewner-bound"),
                DeclarationHandle.Create(Prefix + "mass_lower_bound"),
                H("The mass matrix inequality"),
                StatementSource.FromAuthor(Disp(Call("PosSemidef",
                    Seq(Mass(), Minus, Third(), Cdot, Sp, F.Id("I"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The blocks form a real symmetric matrix. Subtracting "
                    + "one third of the identity turns the energy bound into nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mass-positive-definite"),
                DeclarationHandle.Create(Prefix + "mass_posDef"),
                H("Positive mass"),
                StatementSource.FromAuthor(Disp(Call("PosDef", Mass()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nonzero vector has a positive sum of squares. "
                    + "Its mass energy is therefore strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spatial-loewner-bound"),
                DeclarationHandle.Create(Prefix + "spatial_lower_bound"),
                H("The spatial matrix inequality"),
                StatementSource.FromAuthor(Disp(Call("PosSemidef",
                    Seq(Spatial(), Minus, F.Id("I"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every unperturbed diagonal entry is at least two. "
                    + "The perturbed entry k-b is at least one. Hence subtracting the "
                    + "identity leaves a nonnegative diagonal matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spatial-uniform-energy-bound"),
                DeclarationHandle.Create(Prefix + "spatial_coercive"),
                H("Uniform spatial energy"),
                StatementSource.FromAuthor(Disp(Le(Call("V", F.Id("x")),
                    Call("Q", Spatial(), F.Id("x"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluate the spatial matrix inequality on x."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spatial-positive-definite"),
                DeclarationHandle.Create(Prefix + "spatial_posDef"),
                H("Positive spatial principal part"),
                StatementSource.FromAuthor(Disp(Call("PosDef", Spatial()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every diagonal entry is at least one, hence positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-uniform-coefficient-bound"),
                DeclarationHandle.Create(Prefix + "coefficient_bounds"),
                H("Bounded integer coefficients"),
                StatementSource.FromAuthor(Disp(Call("Coeff", F.Id("n"), F.Id("k"),
                    F.Id("b"), F.Id("i"), F.Id("j")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mass entries belong to minus one, zero, one, and four. "
                    + "Spatial entries belong to zero, k, and k-b. With integer k at least "
                    + "two and integer b between zero and one, all these entries are integers "
                    + "of absolute value at most max(k,4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-integer-block-pencil"),
                DeclarationHandle.Create(Prefix + "uniform_pencil_bounds"),
                H("The uniform integer family"),
                StatementSource.FromAuthor(Disp(Call("Uniform", F.Id("n"), F.Id("k"),
                    F.Id("b")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combine the mass, spatial, and coefficient estimates. "
                    + "The constants one third, one, and max(k,4) do not depend on n. "
                    + "The visible-to-hidden endpoint coefficients are exactly one and "
                    + "the coefficients between adjacent hidden vertices are minus one."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Third() => new Formula.Fraction(D(1), D(3));

    private static Formula Mass() => Call("K", F.Id("n"));

    private static Formula Spatial() => Call("G", F.Id("n"), F.Id("k"), F.Id("b"));

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
