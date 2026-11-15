using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class BellBlocksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks.";

    public DocumentDefinition Create()
    {
        Formula r = F.Id("R"), c = F.Id("C"), rk = F.Id("rk"), rb = F.Id("rb"), ck = F.Id("ck"), cb = F.Id("cb");
        Formula m = F.Id("M"), n = F.Id("N"), bits = Call("Bool"), pairs = Call("prod", Call("Fin", D(2)), Call("Fin", D(2)));
        Formula first = Call("indicator", And(rk, ck)), second = Call("indicator", And(rb, cb));
        Formula count = new Formula.Binary(first, FormulaBinaryOperator.Add, second);
        Formula conclusion = Equal(Call("traceNorm", Call("fourEntries", r, c)), Call("bellValue", count));
        Formula assumptions = Imp(Or(rk, ck), Imp(Or(rb, cb),
            Imp(Call("coordinateKernel", r, rk, rb), Imp(Call("coordinateKernel", c, ck, cb), conclusion))));
        Formula statement = All(m, Call("FiniteType"), All(n, Call("FiniteType"),
            All(r, Seq(pairs, Sp, To, Sp, m), All(c, Seq(pairs, Sp, To, Sp, n),
                All(rk, bits, All(rb, bits, All(ck, bits, All(cb, bits, assumptions))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The four correlated half entries are separated by their row and column coordinate kernels.",
            H("Finite Bell blocks from coordinate kernels"),
            Blocks([
                .. NormInvarianceDescriptions.Items(),
                .. WitnessNormsDescriptions.Items(),
                Describe.Lean(
                DescribeId.Create("coordinate-inclusions-preserve-matrix-units"),
                DeclarationHandle.Create(Prefix + "embedded_single"),
                H("Embedding one matrix unit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary finite row and column types a,b,m,n with decidable equality, "
                    + "injections e from m to a and f from n to b, indices i in m and j in n, and a complex coefficient c, "
                    + "coordinateEmbedding(e) times single(i,j,c) times the adjoint of coordinateEmbedding(f) "
                    + "equals single(e(i),f(j),c). The sparse product has only the selected column and selected row. "
                    + "This identity is used to expand the embedded single-party and Bell density matrices."))),
                DescribeRole.Theorem), Describe.Lean(
                DescribeId.Create("four-half-entry-bell-block-norm"),
                DeclarationHandle.Create(Prefix + "traceNorm_fourEntries"),
                H("Trace norm of a Bell support pattern"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "fourEntries(R,C) is the sum, over the four pairs x in Fin 2 times Fin 2, of the matrix single(R(x),C(x),1/2). "
                    + "The finite row and column types have decidable equality. coordinateKernel(R,rk,rb) means that R(x)=R(y) "
                    + "if and only if rk being true forces equality of the first coordinates and rb being true forces equality of the second coordinates. "
                    + "The two Boolean flags for C have the same meaning. Each coordinate must occur in at least one side. "
                    + "indicator(b) is one for true and zero for false. Thus count is the number of coordinates that occur in both sides. "
                    + "The value bellValue is one at count zero, twice sqrt(1/2) at count one, and two at count two. "
                    + "Coordinate embeddings reduce the arbitrary finite row and column types to the retained coordinates. "
                    + "The nine possible nonempty routing patterns give the scalar identity, constant square, single-column, or singly crossed blocks."))),
                DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("bell-block-values-distinguish-shared-count"),
                    DeclarationHandle.Create(Prefix + "bellValue_injective"),
                    H("The three Bell norms are distinct"),
                    StatementSource.FromAuthor(Disp(Call("injectiveOn", Call("bellValue"), Call("closedNatInterval", D(0), D(2))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The three values are ordered as one, twice sqrt(1/2), and two. Equality of Bell norms therefore recovers the shared-coordinate count whenever both counts are at most two."))),
                    DescribeRole.Theorem)]),
            []));
    }

    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula domain, Formula body) => Seq(Forall, Sp, x, Colon, domain, Comma, Sp, Par(body));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Or, Par(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.And, Par(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Par(x), FormulaLogicOperator.Implies, Par(y));
}

internal static class NormInvarianceDescriptions
{
    private const string Module = "D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks";

    public static DocumentBlock[] Items() => [

            Describe.Lean(
                DescribeId.Create("rectangular-independent-isometries"),
                DeclarationHandle.Create(Module + ".traceNorm_two_isometries"),
                H("Independent isometries preserve the rectangular trace norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A be a complex matrix with finite row and column index sets m and n. "
                    + "Let V have row set a and column set m, and W have row set b and column set n. "
                    + "If V* V and W* W are identity matrices, then the trace norm of V A W* equals "
                    + "the trace norm of A. Here star denotes the conjugate transpose, and the trace "
                    + "norm is Re Tr sqrt(A* A). This directly specializes the existing "
                    + "SicMubCorrelationTraceNormEquality.scaled_isometry_traceNorm at alpha=beta=1. "
                    + "The index sets need not have equal cardinalities, and empty index sets are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coordinate-inclusion-matrix"),
                DeclarationHandle.Create(Module + ".coordinateEmbedding"),
                H("The matrix of a coordinate inclusion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an injection e from m to a, the coordinate inclusion matrix "
                    + "has entry one at row e(j) and column j, and entry zero elsewhere. "
                    + "It includes a vector in the larger coordinate space and sets every unused coordinate to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coordinate-inclusion-isometry"),
                DeclarationHandle.Create(Module + ".coordinateEmbedding_isometry"),
                H("A coordinate inclusion is an isometry"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every injection e from m to a, the product of the conjugate "
                    + "transpose of its coordinate inclusion matrix with that matrix is the identity on m. "
                    + "Distinct columns have disjoint supports, and each column has exactly one entry equal to one. "
                    + "Combining two such inclusions with the rectangular isometry identity preserves the trace norm "
                    + "when an arbitrary finite matrix is included as a block with zero entries outside it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangular-independent-coordinate-reindexing"),
                DeclarationHandle.Create(Module + ".traceNorm_submatrix_equiv"),
                H("Independent bijective reindexing preserves the trace norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite rectangular complex matrix A, a bijection e "
                    + "onto its row index set and a bijection f onto its column index set satisfy "
                    + "traceNorm(A.submatrix e f)=traceNorm(A). The two changes of coordinates are independent. "
                    + "Their inverse coordinate inclusion matrices are isometries, so the rectangular "
                    + "two-isometry identity applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-index-transpose-trace-norm"),
                DeclarationHandle.Create(Module + ".traceNorm_transpose"),
                H("Transpose preserves the trace norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every square complex matrix A on an arbitrary finite index set, "
                    + "traceNorm(A transpose)=traceNorm(A). This is the existing transpose invariance of "
                    + "unitarily invariant norms, transported along a finite indexing equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-index-adjoint-trace-norm"),
                DeclarationHandle.Create(Module + ".traceNorm_conjTranspose"),
                H("Adjoint preserves the trace norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every square complex matrix A on an arbitrary finite index set, "
                    + "traceNorm(A*)=traceNorm(A). This is the existing adjoint invariance of unitarily "
                    + "invariant norms, transported along a finite indexing equivalence. In particular, "
                    + "the trace norms defined using A* A and A A* agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rectangular-adjoint-trace-norm"),
                DeclarationHandle.Create(Module + ".traceNorm_conjTranspose_rect"),
                H("Adjoint preserves the rectangular trace norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite rectangular complex matrix A, traceNorm(A*) "
                    + "equals traceNorm(A). Embed its row and column spaces into their disjoint sum, "
                    + "using independent coordinate isometries. The resulting square matrix and its "
                    + "adjoint have the same trace norm; the two-isometry identity then gives the "
                    + "rectangular equality. The row and column index sets may have different cardinalities."))),
                DescribeRole.Theorem)
    ];
}

internal static class WitnessNormsDescriptions
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("permutation-witness-norms-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public static DocumentBlock[] Items() => [

            Item("traceNorm_of_scalar_gram", "A constant singular value", "Let A be a rectangular complex matrix on finite index types, and let c be a nonnegative real number. If A-adjoint times A is c squared times the identity on the column index type, then traceNorm(A) equals c times the number of columns. The positive square root is c times the identity; zero c and empty index types are included."),
            Item("mixedColumn", "The mixed witness column", "The two-by-one matrix whose entries are both one half.", DescribeRole.Definition),
            Item("traceNorm_mixedColumn", "The mixed column norm", "The trace norm of mixedColumn is the positive square root of one half. Its one-by-one Gram matrix has entry one half."),
            Item("halfIdentity", "Scalar identity blocks", "For a natural number n, halfIdentity(n) is one half times the identity matrix on Fin n.", DescribeRole.Definition),
            Item("traceNorm_halfIdentity", "Scalar identity block norms", "For every natural n, traceNorm(halfIdentity(n)) is n divided by two. In particular the split mixed witness block has norm one and the doubly crossed Bell block has norm two."),
            Item("bellColumn", "The Bell column", "The four-by-one matrix whose entries are all one half.", DescribeRole.Definition),
            Item("traceNorm_bellColumn", "The Bell column norm", "The trace norm of bellColumn is one. Its only Gram entry is one."),
            Item("bellOneCross", "One crossed Bell equality", "The row index is a pair of bits, the column index is a bit, and the entry is one half when the first row bit equals the column bit, and zero otherwise.", DescribeRole.Definition),
            Item("traceNorm_bellOneCross", "The singly crossed Bell norm", "The trace norm of bellOneCross is twice the positive square root of one half. Its Gram matrix is one half times the two-dimensional identity, so its two singular values are both the square root of one half."),
            Item("bellSquare", "The constant Bell square", "The two-by-two matrix whose entries are all one half.", DescribeRole.Definition),
            Item("traceNorm_bellSquare", "The constant Bell square norm", "The trace norm of bellSquare is one. The matrix is positive semidefinite and its trace is one.")
    ];
}
