using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class DensityKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/DensityKernel.";
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula DetSpectral()
    {
        Formula A = F.Id("A");
        Formula hA = F.Id("hA");
        Formula s = F.Id("s");
        Formula i = F.Id("i");
        Formula matrixType = At(Qualified("Matrix"), Iota, Iota, Complexes);
        Formula scalarAction = Seq(Parenthesized(s), Sp, Cdot, Sp, Parenthesized(A));
        Formula factor = At(Qualified("Complex", "ofReal"),
            Add(D(1), Mul(s, At(Qualified("Matrix", "IsHermitian", "eigenvalues"), hA, i))));
        Formula product = Seq(new Formula.Subscript(Prod, Seq(i, Colon, Sp, Iota)), Sp, Parenthesized(factor));
        Formula equality = new Formula.Relation(At(Qualified("Matrix", "det"),
            Add(Typed(D(1), matrixType), scalarAction)), FormulaRelationOperator.Equal, product);
        return All(Iota, Qualified("Type"), Seq(
            OpenBracket, At(Qualified("Fintype"), Iota), CloseBracket, Sp,
            OpenBracket, At(Qualified("DecidableEq"), Iota), CloseBracket, Sp,
            All(A, matrixType, All(hA, At(Qualified("Matrix", "IsHermitian"), A), All(s, Reals, equality)))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integrable common bound and continuity of subentropy on the full density-matrix domain.",
        H("Density-matrix kernels and continuity"),
        Blocks(
            Paragraph(Text("All finite dimensions are allowed. Matrices are positive semidefinite with complex trace one. Their real eigenvalues are nonnegative and sum to one. Unitary diagonalization gives det(I+A/t) as the product of 1+lambda_i/t, so the determinant has positive real part whenever t>0.")),
            Describe.Lean(DescribeId.Create("det-spectral"), DeclarationHandle.Create(Owner + "det_spectral"),
                H("The determinant of a Hermitian interpolation"), StatementSource.FromAuthor(Disp(DetSpectral())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(Paragraph(Text("For any finite Hermitian complex matrix A and real scalar s, the determinant of I+sA is the product of one plus s times each real eigenvalue of A, with each complete real factor embedded into the complex numbers. The scalar action on the left is real scalar multiplication of a complex matrix. Unitary diagonalization conjugates I+sA to the diagonal matrix with these factors; determinant invariance under that conjugation and the determinant formula for a diagonal matrix give the equality. No positivity or trace normalization is required."))), DescribeRole.Theorem),
            Item("spectral_prob", "The spectral probability vector", "A positive semidefinite finite matrix of trace one has nonnegative real eigenvalues summing to one. Positivity supplies the coordinate signs and taking real parts of the spectral trace identity supplies normalization. This interface is used by the Gaussian matrix representation."),
            Item("density_kernel_bounds", "A dimension-independent bound", "The determinant kernel is nonnegative and at most 1/(1+t)^2 for every positive t and every density matrix. The estimate follows from the sharper classical vertex bound after spectral reduction. It includes repeated eigenvalues and zero eigenvalues."),
            Item("integrable_subentropy_kernel", "Absolute integrability", "The continuous kernel on the positive half-line is dominated in absolute value by the common integrable inverse-square function. Hence its defining subentropy integral is absolutely convergent."),
            Item("continuousOn_matrixSubentropy", "Continuity at all density matrices", "The determinant is continuous in the entries, and its real part remains positive on the density domain at each positive t. Dominated convergence with the common function 1/(1+t)^2 gives continuity of Q on the full set of positive trace-one matrices, including its boundary."))));
    private static DocumentBlock.Describe Item(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
