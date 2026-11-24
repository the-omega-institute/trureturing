using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Unistochastic;

internal sealed class UnistochasticTypeIMinusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/Unistochastic/TypeIMinus.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/bengtssonericssonkustadejzyczkowski2004unistochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict Type I− hyperoctant excludes order-four unistochastic matrices.",
        H("Strict Type I− exclusion"),
        Blocks(
            Describe.Lean(DescribeId.Create("hadamard-characters"),
                DeclarationHandle.Create(Prefix + "H"), H("Normalized Hadamard characters"),
                StatementSource.FromAuthor(CharacterFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The four rows of H are (1,1,1), (1,−1,−1), (−1,1,−1), and (−1,−1,1), "
                    + "each divided by 2. The columns are orthonormal and perpendicular to the "
                    + "all-ones vector. Their outer products give the nine coordinates of "
                    + "the affine space of doubly stochastic matrices after centering."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonnegative-coordinate"),
                DeclarationHandle.Create(Prefix + "exists_nonneg_typeIMinus"),
                H("Every unitary has a nonnegative coordinate"),
                StatementSource.FromAuthor(ExclusionFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The theorem answers Bengtsson, Ericsson, Kuś, Tadej, and Życzkowski's question "
                    + "in arXiv:math/0402325v2, §IV, p. 21. Their central-ray exclusion appears in "
                    + "§IV, pp. 19–20, using Appendix C. Row and column permutations preserve "
                    + "unitarity and permute the squared-norm matrix in the same way, so the "
                    + "exclusion also applies to the permutation images of this sector. "
                    + "The star-shapedness question for the full order-four unistochastic set "
                    + "in the same paragraph remains separate.")),
                    Paragraph(Text(
                    "Assuming all nine coordinates are negative, choose a row whose products "
                    + "are bounded by the other rows' products on at least two column pairs. "
                    + "Hadamard sums give the off-diagonals of two planar overlap Gram matrices. "
                    + "The squared norms of the signed Hermitian unitary entries give the "
                    + "diagonal bounds and the exact difference between opposite row pairs. "
                    + "The two selected pairs force strictly larger Schur-complement diagonals "
                    + "and strictly smaller off-diagonal magnitude for the second Gram matrix. "
                    + "Both Schur complements have determinant zero, giving the contradiction."))),
                DescribeRole.Theorem))));

    private static Formula CharacterFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Call("Matrix", Call("Fin", D(4)), Call("Fin", D(3)), real);
        return Disp(Seq(F.Id("H"), Colon, Sp, type));
    }

    private static Formula ExclusionFormula()
    {
        Formula u = F.Id("U"), h = F.Id("H"), i = F.Id("i"), j = F.Id("j");
        Formula four = Call("Fin", D(4)), three = Call("Fin", D(3));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula unitary = Apply(Qualified("Matrix", "unitaryGroup"), four, complex);
        Formula transpose = Apply(Qualified("Matrix", "transpose"), h);
        Formula probability = Apply(Qualified("RHLinalg", "normSqMatrix"), u);
        Formula coordinate = Apply(Seq(Open, transpose, Sp, Cdot, Sp, probability, Sp, Cdot, Sp, h,
            Close), i, j);
        return Disp(Seq(Forall, Sp, Open, u, Colon, Sp, Call("Matrix", four, four, complex),
            Close, Comma, Sp, new Formula.Relation(u, FormulaRelationOperator.MemberOf, unitary),
            Sp, To, Sp, Exists, Sp, Open, i, Sp, j, Colon, Sp, three, Close, Comma, Sp,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, coordinate)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
}
