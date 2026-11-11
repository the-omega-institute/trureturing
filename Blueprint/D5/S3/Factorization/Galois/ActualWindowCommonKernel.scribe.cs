using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class ActualWindowCommonKernelDocument : IScribeDocumentDefinition
{
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
                Blocks(Paragraph(Text("Choose the least intersection dimension among tuples with every coordinate nonzero. Any positive original-label intersection contains a nonzero vector w; the section with coordinate r(i) inverse times w belongs to the original windows, has no zero coordinates, and reconstructs precisely those labels when r(k) is one. This supplies the full comparison with original labels. The common-kernel rank identity then shows that the same chosen tuple maximizes constraint rank. The argument works in any characteristic and for independently scaled windows. The rank optimum over actual tuples alone does not identify an intermediate field or give a subfield dimension formula."))), DescribeRole.Theorem))));

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
