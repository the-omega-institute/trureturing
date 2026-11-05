using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class KiteShapedDoublyPerfectFormDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuadraticForms/grossgoedicke2025artisanal");

    private static Formula N => F.Id("n");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula BinaryField => Call("ZMod", D(2));
    private static Formula Index => Call("Fin", N);
    private static Formula BlockIndex => Call("Sum", Index, Index);
    private static Formula MatrixType => Call("Matrix", Index, Index, BinaryField);
    private static Formula BlockMatrixType => Call("Matrix", BlockIndex, BlockIndex, BinaryField);
    private static Formula Kite => Call("kite", N);
    private static Formula QuadraticForm => Call("quadraticForm", N);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Named(string name) =>
        Seq(Operatorname, Grp(Seq(name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray())));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula FinValue(Formula value) => Typed(Call("Fin.val", value), Naturals);
    private static Formula SeparatingRight(Formula matrix) =>
        Call("Matrix.SeparatingRight", matrix);
    private static Formula ResidueCondition => Ne(new Formula.Modulo(N, D(3)), D(1));

    private static Formula KiteDefinition => All(N, Naturals, All(I, Index, All(J, Index,
        Eq(Typed(Call("kite", N, I, J), BinaryField),
            Call("ite", Le(Add(Add(FinValue(I), FinValue(J)), D(2)), Add(N, D(1))),
                Typed(D(1), BinaryField), Typed(D(0), BinaryField))))));

    private static Formula QuadraticFormDefinition => All(N, Naturals,
        Eq(Typed(QuadraticForm, BlockMatrixType),
            Call("Matrix.fromBlocks", Kite, Typed(D(0), MatrixType),
                Typed(D(0), MatrixType), Kite)));

    private static Formula Claim => All(N, Naturals, Imp(Le(D(1), N),
        And(Call("Matrix.IsSymm", Kite),
            And(SeparatingRight(Kite),
                And(SeparatingRight(QuadraticForm),
                    And(Iff(SeparatingRight(Subtract(Multiply(Kite, Kite),
                            Typed(D(1), MatrixType))), ResidueCondition),
                        Iff(SeparatingRight(Add(QuadraticForm,
                            Call("Matrix.J", Index, BinaryField))), ResidueCondition)))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary kite forms are doubly perfect exactly off one residue modulo three.",
        H("Binary kite-shaped quadratic forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kite"),
                DeclarationHandle.Create(Module + ".kite"),
                H("The kite matrix"),
                StatementSource.FromAuthor(Disp(KiteDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The matrix has entries in the binary field ZMod 2, with rows and columns indexed by Fin n. "
                    + "Fin.val explicitly converts each index to a natural number. Its entry is one exactly when "
                    + "the sum of the two zero-based indices plus two is at most n plus one, and zero otherwise. "
                    + "Adding one to each index gives the source's one-based kite-shaped support "
                    + "(artisanal.tex, line 2316). The definition also includes the empty matrix at n equal to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-form"),
                DeclarationHandle.Create(Module + ".quadraticForm"),
                H("The block-diagonal quadratic form"),
                StatementSource.FromAuthor(Disp(QuadraticFormDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The two diagonal blocks are the same kite matrix, and both off-diagonal blocks are zero. "
                    + "Sum (Fin n) (Fin n) is the disjoint union indexing the two blocks. This is the symmetric "
                    + "coefficient matrix N in the source's quadratic-phase construction "
                    + "(artisanal.tex, lines 2226–2230 and 2315–2316)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The exact residue criterion"),
                StatementSource.FromAuthor(Disp(Eq(Typed(Named("claim"), Named("Prop")), Parenthesized(Claim)))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every positive n, the kite matrix is symmetric and has trivial right kernel, as does its "
                    + "block-diagonal quadratic form. Each of the two remaining right kernels is trivial exactly "
                    + "when n is not one modulo three. Matrix.SeparatingRight expresses triviality of the right "
                    + "kernel for these matrices. The sufficient direction is the source's observation "
                    + "(artisanal.tex, lines 2304–2316); the converse specifies precisely when this construction fails. "
                    + "Matrix.J (Fin n) (ZMod 2) is Mathlib's block matrix with blocks 0, -1, 1, 0. "
                    + "The source uses blocks 0, 1, -1, 0 (lines 349–358); over ZMod 2 the two matrices coincide. "
                    + "The quadratic-phase criterion then identifies the nonsingular cases with doubly perfect "
                    + "quadratic exponentials (lines 2226–2230)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The kite construction succeeds exactly outside one residue"),
                StatementSource.FromAuthor(Disp(Claim)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write K for the kite matrix. Symmetry follows because its entry condition is unchanged "
                        + "when the two indices are exchanged. Define a binary matrix H whose (i,j) entry is the "
                        + "sum of the indicator of i+j+1=n and the indicator of i+j=n, using zero-based natural "
                        + "indices. For any row f, the jth entry of fH is f(n-1-j), together with f(n-j) when j>0. "
                        + "Applying this identity to every row of K gives KH=1: the two threshold indicators "
                        + "cancel in characteristic two except on the diagonal. Thus K has nonzero determinant, "
                        + "and its determinant is one because one is the only nonzero element of ZMod 2.")),
                    Paragraph(Text(
                        "Let T have first diagonal entry zero, every other diagonal entry one, adjacent "
                        + "off-diagonal entries one, and all remaining entries zero. Applying the same column "
                        + "identity to H shows that T=1+HH. To compute d(n+2), reverse both row and "
                        + "column orders of T of size n+2. This leaves the determinant unchanged and places a sparse row and "
                        + "column first. Removing their first indices gives the reversed matrix of size n+1; "
                        + "removing their first two indices gives the reversed matrix of size n. Expansion "
                        + "therefore gives d(n+2)=d(n+1)+d(n), where d(n) is the determinant of T of size n. "
                        + "The initial determinants are d(0)=1 and d(1)=0. Two-step induction, separating the "
                        + "three residues modulo three, yields d(n)=0 when n is one modulo three and d(n)=1 otherwise.")),
                    Paragraph(Text(
                        "The identity KH=1 implies KKHH=1, so KKT=KK+1. In characteristic two, subtracting "
                        + "the identity is the same as adding it. Taking determinants and using det K=1 "
                        + "therefore gives det(KK-1)=det T. The determinant of the block-diagonal quadratic "
                        + "form is the product of its two diagonal determinants, hence is also one.")),
                    Paragraph(Text(
                        "Adding Matrix.J to the quadratic form gives the block matrix with diagonal blocks K "
                        + "and off-diagonal blocks 1. Since K is invertible with inverse H, its Schur complement "
                        + "gives determinant det K times det(K-H). Multiplying K-H by K on the left gives KK-1, "
                        + "so this block determinant equals det(KK-1), and hence det T. Finally, a square matrix "
                        + "over ZMod 2 is right-separating exactly when its determinant is nonzero. The determinant "
                        + "values give the two unconditional trivial-kernel assertions and both equivalences for every positive n."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gross-goedicke-2025-kite-shaped-quadratic-forms"),
                    ResolutionKind.Proved)))));
}
