using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ActualWindowCommonKernelDocument : IScribeDocumentDefinition
{
    private const string HyperplanePrefix = "D5/S3/Factorization/Galois/ActualWindowCommonKernel.HyperplaneRank.";
    private static readonly LibraryNoteRef HyperplaneSource =
        LibraryNoteRef.Create("D5/L/Factorization/razwigderson2019subspace");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common kernels and original window labels", H("Common kernels and original window labels"),
        Blocks(
            Paragraph(Text("Let F be a field and L an extension field of finite dimension over F. Let T be a finite index type with a distinguished index k, and let W assign an F-linear subspace of L to each index. Sections(W) denotes the dependent product of the subspaces W(i); vectors in a section are viewed as elements of L. For nonzero labels r(i), J(W,r) is the intersection of the actual scaled subspaces r(i)W(i). Equivalently, x belongs to J(W,r) exactly when the product of the inverse of r(i) and x belongs to W(i) for every i. Write d(W,r) for its F-dimension, and M(W) for the sum of the F-dimensions of the windows.")),
            Paragraph(Text("For a tuple p, C(W,k,p) sends a section v to the tuple whose i-th coordinate is p(k)v(i) minus p(i)v(k). Its k-th output coordinate is zero. Write R(W,k,p) for the F-dimension of its range, and ratio(k,p)(i) for p(k)/p(i). All these objects lie in the given extension field.")),
            Describe.Lean(DescribeId.Create("actual-window-common-kernel-rank"),
                DeclarationHandle.Create("D5/S3/Factorization/Galois/ActualWindowCommonKernel.common_kernel_rank_identity"),
                H("Common kernel rank and positive intersection"),
                StatementSource.FromAuthor(Disp(RankIdentity())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Projection of a kernel vector to coordinate k is an F-linear equivalence onto J(W,ratio(k,p)). The inverse reconstructs every coordinate as p(i)/p(k) times that one vector. Thus all window conditions constrain the same vector. Rank-nullity gives the displayed equality, and p(k) is a nonzero element of the intersection. A singleton index type gives the zero constraint and the original window."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-window-joint-rank-minimizer"),
                DeclarationHandle.Create("D5/S3/Factorization/Galois/ActualWindowCommonKernel.exists_joint_rank_minimizer"),
                H("Simultaneous original-label attainment"),
                StatementSource.FromAuthor(Disp(JointMinimum())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the least intersection dimension among tuples with every coordinate nonzero. Any positive original-label intersection contains a nonzero vector w; the section with coordinate r(i) inverse times w belongs to the original windows, has no zero coordinates, and reconstructs precisely those labels when r(k) is one. This supplies the full comparison with original labels. The common-kernel rank identity then shows that the same chosen tuple maximizes constraint rank. The argument works in any characteristic and for independently scaled windows. The rank optimum over actual tuples alone does not identify an intermediate field or give a subfield dimension formula."))), DescribeRole.Theorem),
            Paragraph(Text("UNVERIFIED source drafts: the following partition-rank statements and their proof paths have no current compilation, axiom-closure, emitted mirror or registration evidence. They state the deterministic general-position implication and its actual common-row application. They do not establish that an algebraically independent normal satisfies general position, or that an optimizing partition descends to an actual intermediate field.")),
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
                Blocks(Paragraph(Text("The common rows for a fixed sigma span BF(b)(sigma) intersect ker(phi): the linear map v to phi(blockRows(b,sigma,k))v minus phi(v)blockRows(b,sigma,k) maps the uncut span onto that intersection whenever its distinguished coefficient is nonzero. The span of the uncut subspaces for A is the product, over coordinate blocks i, of span(b(i,sigma): sigma in A). Thus its dimension is the sum of q(b,A,i). Substituting these actual row spaces into the attaining-partition theorem gives the displayed equality and every partition upper bound. This is a live mathematical consumer of the recursive partition construction.")),
                    Paragraph(Text("For R5 (31.5)-(31.7), take the scalar field to be the fraction field K(z) over the normal closure K, I to be the embedding type Omega, B to be the window indices, J(i) to index the chosen basis of X(i), and b(i,sigma)(j)=sigma(x(i,j)) after scalar extension. Take s to be all embeddings, k the first window and phi(v)=sum over i,j of z(i,j)v(i,j). Then phi(blockRows(b,sigma,i)) is U(i,sigma), and the displayed rows are exactly U(1,sigma) times the i-th block row minus U(i,sigma) times the first block row. The nonzero U(1,sigma) and GP premises still need an actual generic-parameter proof. The unique fewest-block optimum, Galois invariance, descent inside the original ratio field, the rank of the original polynomial matrix, a nonzero original-coefficient minor, and original-F specialization remain outside these statements. No maximizing field or original-label tuple is produced here."))), DescribeRole.Theorem))));

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

    private static Formula RankIdentity()
    {
        Formula p = I("p");
        Formula labels = App(I("ratio"), I("k"), p);
        Formula result = And(Eq(Seq(Rank(p), Plus, Dimension(labels)), App(I("M"), I("W"))),
            Rel(D(0), FormulaRelationOperator.LessThan, Dimension(labels)));
        return Inputs(true, All("p", Sections(), Imp(Nonzero(p), result)));
    }

    private static Formula JointMinimum()
    {
        Formula p = I("p");
        Formula maximum = All("q", Sections(), Imp(Nonzero(I("q")),
            Rel(Rank(I("q")), FormulaRelationOperator.LessThanOrEqual, Rank(p))));
        Formula minimum = All("r", Arrow(I("T"), I("L")), Imp(Nonzero(I("r")),
            Imp(Eq(App(I("r"), I("k")), D(1)),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, Dimension(I("r"))),
                Rel(Dimension(App(I("ratio"), I("k"), p)),
                    FormulaRelationOperator.LessThanOrEqual, Dimension(I("r")))))));
        return Inputs(false, Imp(All("i", I("T"),
            Rel(App(I("W"), I("i")), FormulaRelationOperator.NotEqual, Q("Bot", "bot"))),
            Ex("p", Sections(), And(Nonzero(p), And(maximum, minimum)))));
    }

    private static Formula Inputs(bool fintype, Formula body)
    {
        body = All("W", Arrow(I("T"), App(I("Submodule"), I("F"), I("L"))), All("k", I("T"), body));
        body = Inst(App(I("FiniteDimensional"), I("F"), I("L")), body);
        body = Inst(App(I(fintype ? "Fintype" : "Finite"), I("T")), body);
        body = Inst(App(I("Algebra"), I("F"), I("L")), body);
        body = Inst(App(I("Field"), I("L")), body);
        body = Inst(App(I("Field"), I("F")), body);
        return All("F", Ty(), All("L", Ty(), All("T", Ty(), body)));
    }

    private static Formula Sections() => App(I("Sections"), I("W"));
    private static Formula Dimension(Formula r) => App(I("d"), I("W"), r);
    private static Formula Rank(Formula p) => App(I("R"), I("W"), I("k"), p);
    private static Formula Nonzero(Formula p) => All("i", I("T"),
        Rel(App(p, I("i")), FormulaRelationOperator.NotEqual, D(0)));
    private static Formula I(string name) => F.Id(name);
    private static Formula Ty() => Seq(I("Type"), Star);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(I(a)), Dot, Operatorname, Grp(I(b)));
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
