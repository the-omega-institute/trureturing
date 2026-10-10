using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class ContractionBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/aubrun2024completely");
    private static readonly Formula N = F.Id("n"), M = F.Id("m"), C = F.Id("C"), Hm = F.Id("H");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite complex Euclidean contraction has a rank-one phase decomposition with twice as many terms as its dimension. This decomposition makes the scalar shift mI + H separable for a Hermitian Euclidean contraction on a product of dimensions m and n.",
        H("Contraction decompositions and separable scalar shifts"),
        Blocks(
            Node("separableCone_sum", "Finite sums preserve separability", SeparableSum(),
                "For any finite index type, a sum of separable matrices is separable. The empty sum is the zero matrix, and adjoining one summand preserves separability by addition. This includes zero dimensions."),
            Node("contraction_decomposition", "A finite rank-one phase decomposition", Decomposition(),
                "The vectors are indexed by Fin n ⊕ Fin n, including the empty family when n is zero. Their rank-one matrices sum to the identity, and multiplying them by scalars of modulus one reconstructs C. The square root of I − C* C supplies an orthonormal family whose first coordinates are the columns of C. Extending it to an orthonormal basis gives a unitary dilation. The spectral theorem for normal matrices diagonalizes this unitary dilation in an orthonormal basis; unitarity forces each diagonal eigenvalue to have modulus one. Restricting the vectors to the first n coordinates gives the stated decomposition."),
            Node("separableCone_scalar_add_of_opNorm_le_one", "Separable middle rays", MiddleRays(),
                "Aubrun--Davidson--Muller-Hermes--Paulsen--Rahaman Theorem 3.7, printed page 9, gives d₁(M_n) = n. The formal scalar-shift statement is its dual form under separable and block-positive cone duality, with the factor labels exchanged. The theorem's proof uses a separable block operator with identity diagonal blocks and a scaled contraction off the diagonal. The bound here quantifies all complex coordinate vectors and takes the norm after WithLp.toLp 2, so both norms are Euclidean. The dimensions m and n may be zero; these cases give the zero matrix. Each diagonal block I + Hii is positive semidefinite. Each off-diagonal block Hij is a contraction; its phase decomposition expresses the two-by-two block with identity diagonal as a sum of Kronecker products of positive semidefinite rank-one matrices, the block-separability statement of Gurvits--Barnum Proposition 1, printed page 2. Embedding these blocks and adding the diagonal terms yields mI + H. The separable cone here means a finite sum of Kronecker products of positive semidefinite factors.",
                AssessedProvenance.FromLiterature(Source))), []));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("contraction-blocks-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula SeparableSum()
    {
        Formula index = F.Id("I"), f = F.Id("f"), i = F.Id("i");
        Formula product = Call("Prod", Fin(M), Fin(N));
        Formula premise = All(i, index,
            QCall("D5.S3.Resource.CompositeCones", "separableCone", App(f, i)));
        Formula conclusion = QCall("D5.S3.Resource.CompositeCones", "separableCone",
            SumOver(i, index, App(f, i)));
        Formula finite = Seq(OpenBracket, Call("Fintype", index), CloseBracket);
        return All(M, Nat(), All(N, Nat(), All(index, Call("Type"),
            Seq(finite, Comma, Sp,
                All(f, Arrow(index, Mat(product)), Imp(premise, conclusion))))));
    }

    private static Formula Decomposition()
    {
        Formula a = F.Id("a"), c = F.Id("c"), r = F.Id("r");
        Formula index = Call("Sum", Fin(N), Fin(N));
        Formula ar = App(a, r), cr = App(c, r);
        Formula phases = All(r, index, Eq(Norm(cr), D(1)));
        Formula identity = Eq(SumOver(r, index, Outer(ar)), D(1));
        Formula reconstruction = Eq(SumOver(r, index, Smul(cr, Outer(ar))), C);
        return All(N, Nat(), All(C, Mat(Fin(N)), Imp(
            Positive(Sub(D(1), Mul(Adj(C), C))),
            Some(a, Arrow(index, Arrow(Fin(N), Complex())),
                Some(c, Arrow(index, Complex()), And(phases, And(identity, reconstruction)))))));
    }

    private static Formula MiddleRays()
    {
        Formula x = F.Id("x"), index = Call("Prod", Fin(M), Fin(N));
        Formula bound = All(x, Arrow(index, Complex()),
            Le(Norm(L2(QCall("Matrix", "mulVec", Hm, x))), Norm(L2(x))));
        Formula scalar = Parenthesized(Seq(M, Sp, Colon, Sp, Complex()));
        return All(M, Nat(), All(N, Nat(), All(Hm, Mat(index),
            Imp(QCall("Matrix", "IsHermitian", Hm), Imp(bound,
                QCall("D5.S3.Resource.CompositeCones", "separableCone",
                    Add(Smul(scalar, D(1)), Hm)))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return App(result, args);
    }
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula SumOver(Formula name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(name, Sp, Colon, Sp, type)), Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Mat(Formula i) => Call("Matrix", i, i, Complex());
    private static Formula Adj(Formula a) => QCall("Matrix", "conjTranspose", a);
    private static Formula Positive(Formula a) => QCall("Matrix", "PosSemidef", a);
    private static Formula Outer(Formula a) => QCall("Matrix", "vecMulVec", a, Call("star", a));
    private static Formula L2(Formula a) => QCall("WithLp", "toLp", D(2), a);
}
