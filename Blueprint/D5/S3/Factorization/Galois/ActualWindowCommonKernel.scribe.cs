using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ActualWindowCommonKernelDocument : IScribeDocumentDefinition
{
    private const string HyperplanePrefix = "D5/S3/Factorization/Galois/ActualWindowCommonKernel.";
    private static readonly LibraryNoteRef HyperplaneSource =
        LibraryNoteRef.Create("D5/L/Factorization/razwigderson2019subspace");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common hyperplane cuts and embedding constraint rigidity", H("Common hyperplane cuts and embedding constraint rigidity"),
        Blocks(
            Paragraph(Text("For the next statement K is a field, E a finite-dimensional K-vector space, I any index type, V(i) a K-subspace of E, phi a K-linear functional and s a finite subset of I. Write S(V,A) for the supremum of V(i) over i in A, T(V,phi,A) for the supremum of V(i) intersect ker(phi) over i in A, and C(V,P) for the sum over B in P.parts of dim_K S(V,B) minus one. Finpartition(s) means a finite partition of s into nonempty disjoint blocks; the empty s has the empty partition. GP(V,phi,s) means both: no V(i), for i in s, is contained in ker(phi); and for all finite A,B,C contained in s, if (T(V,phi,A)+S(V,B)) intersect (T(V,phi,A)+S(V,C)) is contained in ker(phi), then that intersection equals T(V,phi,A). The middle family A may be empty, as in the footnote to Definition 5.1 and the base case of Lemma 5.3.")),
            Describe.Lean(DescribeId.Create("common-hyperplane-partition-rank"),
                DeclarationHandle.Create(HyperplanePrefix + "hyperplane_partition_rank"),
                H("An attaining partition for a hyperplane in general position"),
                StatementSource.FromAuthor(Disp(HyperplanePartitionRank())),
                AssessedProvenance.FromLiterature(HyperplaneSource),
                Blocks(Paragraph(Text("This is the deterministic implication of Raz and Wigderson, Theorem 5.2. Let T be the total cut span and group i and j when T+V(i)=T+V(j). Each such extension has dimension dim(T)+1. Distinct extensions therefore intersect precisely in T. For a union A of intervening classes, the general-position intersection law applied to T(A)+S(B) and T(A)+S(C) removes every dependence between the first and last classes modulo T(A). Induction gives supremum independence of all class cut spans. If there is only one class, the entire uncut span has dimension dim(T)+1 and the one-block partition is tight. Otherwise every class is a proper subfamily; recursively choose tight partitions there and combine them by Finpartition.bind. This constructs a partition whose cost is exactly the cut rank. The opposite inequality follows by bounding each block cut inside its uncut span intersect ker(phi).")),
                    Paragraph(Text("The new recursive partition construction and its independence argument are the necessary non-normalization steps. The one-dimensional extension calculations, finite-sup dimension identities and finite-partition constructors reuse pinned Mathlib. No claim of mathematical novelty is made for the classical theorem. The result is a necessary intermediate for R5 (31.7), not the complete generic rank or (31.10)."))), DescribeRole.Theorem),
            Paragraph(Text("For the block statement, B is a finite block type and J assigns a finite coordinate type J(i) to each i in B. BlockSpace(K,B,J) is the dependent product of J(i) to K. An array b has type (i in B) to (I to J(i) to K). The row blockRows(b,sigma,i) places b(i,sigma) in coordinate block i and is zero elsewhere. BF(b)(sigma) is the span of all these block-supported rows. Write q(b,A,i) for dim_K span of b(i,sigma) over sigma in A, BC(b,P) for the sum over A in P.parts of (sum over i in B of q(b,A,i)) minus one, and R(b,phi,k,s) for the dimension of the span of all rows phi(blockRows(b,sigma,k)) times blockRows(b,sigma,i) minus phi(blockRows(b,sigma,i)) times blockRows(b,sigma,k), with sigma in s and i in B. In this definition the SAME phi and k are used in every row; the i=k row is zero.")),
            Describe.Lean(DescribeId.Create("actual-common-block-partition-rank"),
                DeclarationHandle.Create(HyperplanePrefix + "block_common_rows_partition_rank"),
                H("The common-constraint block row partition formula"),
                StatementSource.FromAuthor(Disp(BlockPartitionRank())),
                AssessedProvenance.FromRepo(HyperplaneSource),
                Blocks(Paragraph(Text("The common rows for a fixed sigma span BF(b)(sigma) intersect ker(phi): the linear map v to phi(blockRows(b,sigma,k))v minus phi(v)blockRows(b,sigma,k) maps the uncut span onto that intersection whenever its distinguished coefficient is nonzero. The span of the uncut subspaces for A is the product, over coordinate blocks i, of span(b(i,sigma): sigma in A). Thus its dimension is the sum of q(b,A,i). Substituting these actual row spaces into the attaining-partition theorem gives the displayed equality and every partition upper bound. The embedding-kernel rigidity theorem below uses both the attaining partition and these universal partition bounds.")),
                    Paragraph(Text("For R5 (31.5)-(31.7), take the scalar field to be the fraction field K(z) over the normal closure K, I to be the embedding type Omega, B to be the window indices, J(i) to index the chosen basis of X(i), and b(i,sigma)(j)=sigma(x(i,j)) after scalar extension. Take s to be all embeddings, k the first window and phi(v)=sum over i,j of z(i,j)v(i,j). Then phi(blockRows(b,sigma,i)) is U(i,sigma), and the displayed rows are exactly U(1,sigma) times the i-th block row minus U(i,sigma) times the first block row. SymbolicHyperplaneGeneralPosition.symbolic_general_position proves both clauses of this GP premise for scalar extensions of constant subspaces and independent symbolic normal coordinates, including empty and overlapping subfamilies. Its symbolic_block_common_rows_partition_rank consumes that proof and proves the distinguished symbolic coefficient nonzero from a nonzero base row, yielding this common-row partition formula without a GP premise. The new proof uses directional derivations of the rational function field; individual nonvanishing by itself would not discharge the intersection clause. The unique fewest-block optimum, Galois invariance, descent inside the original ratio field, the rank of the original polynomial matrix, a nonzero original-coefficient minor, and original-F specialization remain outside these statements. No maximizing field or original-label tuple is produced here."))), DescribeRole.Theorem),
            Paragraph(Text("For the rigidity statement, F and D are fields, D and K are F-algebras, emb is a finite family of F-algebra embeddings D to K, X(i) is an F-subspace of D, and x(i) is an F-basis of X(i) indexed by J(i). Set ER(emb,X,x)(i,sigma,j)=emb(sigma)(x(i,j)). CoefficientSpace(K,B,J) is the space of K-valued functions on the pairs (i,j). A coefficient tuple z is indexed by those pairs; M is the sum of the cardinalities of J(i). Let N(z)(v)=sum over (i,j) of v(i,j)z(i,j). CM(b,phi,k) has rows indexed by (sigma,i) and columns by (j,l); its row is the flattened vector phi(blockRows(b,sigma,k)) blockRows(b,sigma,i) minus phi(blockRows(b,sigma,i)) blockRows(b,sigma,k). Ker(CM) means the kernel of its multiplication map on coefficient columns. Line(K,z) is the K-linear span of z. Write GPall(b,N(z)) for GP(BF(b),N(z),univ), NZall(b,N(z),k) for nonvanishing of every distinguished coefficient, and BC(b,P) for the partition cost already defined.")),
            Describe.Lean(DescribeId.Create("actual-embedding-common-kernel-rigidity"),
                DeclarationHandle.Create(HyperplanePrefix + "embedding_common_kernel_rigidity"),
                H("Rigidity of the actual simultaneous embedding constraints"),
                StatementSource.FromAuthor(Disp(EmbeddingRigidity())),
                AssessedProvenance.FromRepo(HyperplaneSource),
                Blocks(Paragraph(Text("The matrix here acts on an actual coefficient column c. At (sigma,i) its value is U(k,sigma) times sum over j of emb(sigma)(x(i,j))c(i,j), minus U(i,sigma) times sum over j of emb(sigma)(x(k,j))c(k,j). Hence its kernel is the simultaneous embedding-coordinate version of the common constraint, rather than just an abstract cut span. The same z is in this kernel, since the two products U(k,sigma)U(i,sigma) cancel. Flattening dependent coordinate blocks is a linear equivalence; pinned Mathlib row-rank equality identifies the matrix rank with the common-row span rank. Rank-nullity and the nonzero kernel vector z show that the kernel has dimension at least one. If the kernel is Line(K,z), its dimension is one, and each partition bound forces cost at least M-1. Conversely, applying the lower threshold to the attaining partition forces the kernel dimension to be one. The inclusion Line(K,z) in the kernel is then equality. Thus all simultaneous coefficient solutions are scalar multiples of this same tuple exactly under the stated partition criterion.")),
                    Paragraph(Text("For the source correspondence, take K=K_0(z) with K_0 the normal closure, emb the complete family Hom_F(D,K_0) followed by scalar inclusion, X and x the normalized windows and bases of (31.5), and k=1. This theorem is a conditional rigidity consequence of (31.5)-(31.7) for the scalar-extended embedding-coordinate constraint. Its premises are the explicit general-position law, nonzero distinguished coefficients, and a nonzero common coefficient tuple. It assumes neither a rank formula nor genericity, field descent, original-F specialization, or (31.10). The symbolic general-position and distinguished-coefficient hypotheses are discharged for constant rows in SymbolicHyperplaneGeneralPosition. Establishing the original h-1 row basis and the actual embedding dimension and distinctness identifications, transferring the embedding output coordinates to the original polynomial map, Galois descent, and returning an original-F attaining tuple remain separate obligations. Registration for these public targets is unfinished; no declared_validated status is asserted."))), DescribeRole.Theorem))));

    private static Formula HyperplanePartitionRank()
    {
        Formula rank = App(I("dim"), I("K"), App(I("T"), I("V"), I("phi"), I("s")));
        Formula costP = App(I("C"), I("V"), I("P"));
        Formula costQ = App(I("C"), I("V"), I("Q"));
        Formula result = Ex("P", App(I("Finpartition"), I("s")),
            And(Eq(rank, costP), All("Q", App(I("Finpartition"), I("s")),
                Rel(rank, FormulaRelationOperator.LessThanOrEqual, costQ))));
        result = All("V", Arrow(I("I"), App(I("Submodule"), I("K"), I("E"))),
            All("phi", App(I("LinearMap"), I("K"), I("E"), I("K")),
            All("s", App(I("Finset"), I("I")),
                Imp(App(I("GP"), I("V"), I("phi"), I("s")), result))));
        result = Inst(App(I("FiniteDimensional"), I("K"), I("E")), result);
        result = Inst(App(I("Module"), I("K"), I("E")), result);
        result = Inst(App(I("AddCommGroup"), I("E")), result);
        result = Inst(App(I("Field"), I("K")), result);
        return All("K", Ty(), All("E", Ty(), All("I", Ty(), result)));
    }

    private static Formula BlockPartitionRank()
    {
        Formula b = I("b");
        Formula rank = App(I("R"), b, I("phi"), I("k"), I("s"));
        Formula result = Ex("P", App(I("Finpartition"), I("s")),
            And(Eq(rank, App(I("BC"), b, I("P"))),
                All("Q", App(I("Finpartition"), I("s")),
                    Rel(rank, FormulaRelationOperator.LessThanOrEqual, App(I("BC"), b, I("Q"))))));
        Formula nonzero = All("sigma", I("I"), Imp(
            Rel(I("sigma"), FormulaRelationOperator.MemberOf, I("s")),
            Rel(App(I("phi"), App(I("blockRows"), b, I("sigma"), I("k"))),
                FormulaRelationOperator.NotEqual, D(0))));
        result = Imp(nonzero, Imp(App(I("GP"), App(I("BF"), b), I("phi"), I("s")), result));
        result = All("b", All("i", I("B"), Arrow(I("I"), Arrow(App(I("J"), I("i")), I("K")))),
            All("phi", App(I("LinearMap"), I("K"), App(I("BlockSpace"), I("K"), I("B"), I("J")), I("K")),
            All("k", I("B"), All("s", App(I("Finset"), I("I")), result))));
        result = Inst(All("i", I("B"), App(I("Fintype"), App(I("J"), I("i")))), result);
        result = Inst(App(I("Fintype"), I("B")), result);
        result = Inst(App(I("Field"), I("K")), result);
        return All("K", Ty(), All("I", Ty(), All("B", Ty(), All("J", Arrow(I("B"), Ty()), result))));
    }

    private static Formula EmbeddingRigidity()
    {
        Formula b = App(I("ER"), I("emb"), I("X"), I("x"));
        Formula normal = App(I("N"), I("z"));
        Formula matrix = App(I("CM"), b, normal, I("k"));
        Formula cost = All("P", App(I("Finpartition"), App(I("univ"), I("I"))),
            Rel(Seq(I("M"), Minus, D(1)), FormulaRelationOperator.LessThanOrEqual,
                App(I("BC"), b, I("P"))));
        Formula result = new Formula.Logic(
            Eq(App(I("Ker"), matrix), App(I("Line"), I("K"), I("z"))),
            FormulaLogicOperator.Iff, cost);
        result = Imp(Rel(I("z"), FormulaRelationOperator.NotEqual, D(0)),
            Imp(App(I("NZall"), b, normal, I("k")),
                Imp(App(I("GPall"), b, normal), result)));
        result = All("emb", Arrow(I("I"), App(I("AlgHom"), I("F"), I("D"), I("K"))),
            All("X", Arrow(I("B"), App(I("Submodule"), I("F"), I("D"))),
            All("x", All("i", I("B"), App(I("Basis"), App(I("J"), I("i")), I("F"), App(I("X"), I("i")))),
            All("z", App(I("CoefficientSpace"), I("K"), I("B"), I("J")),
            All("k", I("B"), result)))));
        result = Inst(All("i", I("B"), App(I("Fintype"), App(I("J"), I("i")))), result);
        result = Inst(App(I("Fintype"), I("B")), result);
        result = Inst(App(I("Fintype"), I("I")), result);
        result = Inst(App(I("Algebra"), I("F"), I("K")), result);
        result = Inst(App(I("Algebra"), I("F"), I("D")), result);
        result = Inst(App(I("Field"), I("K")), result);
        result = Inst(App(I("Field"), I("D")), result);
        result = Inst(App(I("Field"), I("F")), result);
        return All("F", Ty(), All("D", Ty(), All("K", Ty(), All("I", Ty(),
            All("B", Ty(), All("J", Arrow(I("B"), Ty()), result))))));
    }

    private static Formula I(string name) => F.Id(name);
    private static Formula Ty() => Seq(I("Type"), Star);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
}
