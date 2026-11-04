using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class HermitianEigenvaluePerturbationDocument : IScribeDocumentDefinition
{
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Public declarations of HermitianEigenvaluePerturbation, with complete parameters and the Lean operations.",
        H("HermitianEigenvaluePerturbation"),
        Blocks(
            Describe.Lean(DescribeId.Create("finrank-span-image"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.finrank_span_image"),
                H("finrank_span_image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The complex span of a selected finite orthonormal subfamily has dimension equal to the number of selected indices. No completeness or finite-dimensional ambient instance is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sum-sq-norm-repr-eq-sq-norm"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.sum_sq_norm_repr_eq_sq_norm"),
                H("sum_sq_norm_repr_eq_sq_norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The sum of squared norms of all orthonormal-basis coordinates equals the squared norm of the vector. No completeness or additional finite-dimensional instance is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("re-inner-apply-self-eq-sum-eigenvalues-mul-sq"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.re_inner_apply_self_eq_sum_eigenvalues_mul_sq"),
                H("re_inner_apply_self_eq_sum_eigenvalues_mul_sq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("For a symmetric endomorphism of a finite-dimensional complex inner-product space, the real quadratic form is the sum of its eigenvalues times the squared eigenbasis coordinates. The basis index n is identified with the finrank by the explicit equality hn."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-eigenvalue-sub-eigenvalue-le-norm"), DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalue_sub_eigenvalue_le_norm"), H("abs_eigenvalue_sub_eigenvalue_le_norm"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("T"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, new Formula.Subscript(To, F.Id("L")), Sp, Seq(OpenBracket, Seq(Mathbb,Grp(F.Id("C"))), CloseBracket), Sp, Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))), Sp, new Formula.Subscript(To, F.Id("L")), Sp, Seq(OpenBracket, Seq(Mathbb,Grp(F.Id("C"))), CloseBracket), Sp, Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hT"), Sp, Colon, Sp, Parenthesized(Call("val", F.Id("T"))), Sp, Dot, Sp, Seq(Operatorname,Grp(F.Id("IsSymmetric"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hS"), Sp, Colon, Sp, Parenthesized(Call("val", F.Id("S"))), Sp, Dot, Sp, Seq(Operatorname,Grp(F.Id("IsSymmetric"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hn"), Sp, Colon, Sp, Seq(Seq(Operatorname,Grp(F.Id("Module"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("finrank")))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("d"))))), Sp, Eq, Sp, F.Id("n"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, new Formula.Absolute(Seq(Seq(F.Id("hT"), Dot, Sp, Seq(Operatorname,Grp(F.Id("eigenvalues")))), Sp, F.Id("hn"), Sp, F.Id("k"), Sp, Minus, Sp, Seq(F.Id("hS"), Dot, Sp, Seq(Operatorname,Grp(F.Id("eigenvalues")))), Sp, F.Id("hn"), Sp, F.Id("k"))), Sp, Leq, Sp, new Formula.Norm(Seq(F.Id("T"), Sp, Minus, Sp, F.Id("S")))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("norm-toeuclideanlin-le-of-entry-le"), DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le"), H("norm_toEuclideanLin_le_of_entry_le"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("Matrix"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb,Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, new Formula.Norm(Seq(F.Id("A"), Sp, F.Id("i"), Sp, F.Id("j"))), Sp, Leq, Sp, Varepsilon)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("EuclideanSpace"))), Sp, Seq(Mathbb,Grp(F.Id("C"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))), Sp, Comma, Sp, new Formula.Norm(Seq(Parenthesized(Seq(Seq(Seq(Operatorname,Grp(F.Id("Matrix"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("toEuclideanLin")))), Sp, F.Id("A"))), Sp, F.Id("x"))), Sp, Leq, Sp, Call("val", F.Id("n")), Sp, Cdot, Sp, Varepsilon, Sp, Cdot, Sp, new Formula.Norm(F.Id("x"))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-eigenvalues0-sub-le-norm"), DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm"), H("abs_eigenvalues0_sub_le_norm"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("Matrix"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb,Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("B"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("Matrix"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb,Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, Seq(F.Id("A"), Dot, Sp, Seq(Operatorname,Grp(F.Id("IsHermitian")))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hB"), Sp, Colon, Sp, Seq(F.Id("B"), Dot, Sp, Seq(Operatorname,Grp(F.Id("IsHermitian")))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Seq(Seq(Operatorname,Grp(F.Id("Fintype"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("card")))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Comma, Sp, new Formula.Absolute(Seq(Seq(F.Id("hA"), Dot, Sp, new Formula.Subscript(Seq(Operatorname,Grp(F.Id("eigenvalues"))),D(0))), Sp, F.Id("k"), Sp, Minus, Sp, Seq(F.Id("hB"), Dot, Sp, new Formula.Subscript(Seq(Operatorname,Grp(F.Id("eigenvalues"))),D(0))), Sp, F.Id("k"))), Sp, Leq, Sp, new Formula.Norm(Seq(Seq(Seq(Operatorname,Grp(F.Id("Matrix"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("toEuclideanCLM")))), Sp, Parenthesized(Seq(F.Id("A"), Sp, Minus, Sp, F.Id("B")))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-eigenvalues0-sub-le-of-entry-le"), DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_of_entry_le"), H("abs_eigenvalues0_sub_le_of_entry_le"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("N"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("Matrix"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb,Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Seq(Operatorname,Grp(F.Id("Ahat"))), Sp, Colon, Sp, Seq(Operatorname,Grp(F.Id("Matrix"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))), Sp, Seq(Mathbb,Grp(F.Id("C"))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("hA"), Sp, Colon, Sp, Seq(F.Id("A"), Dot, Sp, Seq(Operatorname,Grp(F.Id("IsHermitian")))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Seq(Operatorname,Grp(F.Id("hAhat"))), Sp, Colon, Sp, Seq(Seq(Operatorname,Grp(F.Id("Ahat"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("IsHermitian")))))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(Varepsilon, Sp, Colon, Sp, Seq(Mathbb,Grp(F.Id("R"))))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, new Formula.Norm(Seq(Seq(Operatorname,Grp(F.Id("Ahat"))), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Minus, Sp, F.Id("A"), Sp, F.Id("i"), Sp, F.Id("j"))), Sp, Leq, Sp, Varepsilon)), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, F.Id("Fin"), Sp, Parenthesized(Seq(Seq(Seq(Operatorname,Grp(F.Id("Fintype"))), Dot, Sp, Seq(Operatorname,Grp(F.Id("card")))), Sp, Parenthesized(Seq(F.Id("Fin"), Sp, F.Id("n"))))))), Sp, Comma, Sp, new Formula.Absolute(Seq(Seq(Seq(Operatorname,Grp(F.Id("hAhat"))), Dot, Sp, new Formula.Subscript(Seq(Operatorname,Grp(F.Id("eigenvalues"))),D(0))), Sp, F.Id("k"), Sp, Minus, Sp, Seq(F.Id("hA"), Dot, Sp, new Formula.Subscript(Seq(Operatorname,Grp(F.Id("eigenvalues"))),D(0))), Sp, F.Id("k"))), Sp, Leq, Sp, Call("val", F.Id("n")), Sp, Cdot, Sp, Varepsilon))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
                Blocks(Paragraph(Text("The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion."))), DescribeRole.Theorem),
            OwnerNode("exists-unit-vector-re-inner-le-eigenvalue", "exists_unit_vector_re_inner_le_eigenvalue",
                UnitVectorFormula(), "Every subspace of dimension k plus one contains a unit vector whose real Rayleigh value is at most the k-th ordered eigenvalue."),
            OwnerNode("exists-submodule-forall-unit-eigenvalue-le-re-inner", "exists_submodule_forall_unit_eigenvalue_le_re_inner",
                SubmoduleFormula(), "There is a subspace of dimension k plus one on which every unit vector has real Rayleigh value at least the k-th ordered eigenvalue."),
            OwnerNode("abs-eigenvalue-sub-eigenvalue-le", "abs_eigenvalue_sub_eigenvalue_le",
                PerturbationFormula(), "A pointwise norm bound on the difference of symmetric linear maps bounds the difference of corresponding ordered eigenvalues."))));

    private static DocumentBlock OwnerNode(string id, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/SpectralTopology/HermitianEigenvaluePerturbation." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Eigenstructure/leanpool2026hermitianeigenvalueperturbation")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula OId(string name) => F.Id(name);
    private static Formula OType(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula OCall(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(OId(name))), [.. args]);
    private static Formula OQualified(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(OId(owner)), Dot, Operatorname, Grp(OId(name))), [.. args]);
    private static Formula OAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula OExists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula OEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula OLe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula OMem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula OAnd(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula OImp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula OLinearMap() => Seq(OId("E"), Sp, new Formula.Subscript(To, OId("L")),
        OpenBracket, OType("Complex"), CloseBracket, Sp, OId("E"));
    private static Formula OSubmodule() => OCall("Submodule", OType("Complex"), OId("E"));
    private static Formula ORank(Formula space) => OQualified("Module", "finrank", OType("Complex"), space);
    private static Formula ODimension() => new Formula.Binary(OQualified("Fin", "val", OId("k")), FormulaBinaryOperator.Add, D(1));
    private static Formula OEigen(string hypothesis) =>
        new Formula.Apply(Seq(OId(hypothesis), Dot, Operatorname, Grp(OId("eigenvalues"))), [OId("hn"), OId("k")]);
    private static Formula ORayleigh() => OQualified("RCLike", "re",
        OCall("inner", OType("Complex"), new Formula.Apply(OId("T"), [OId("x")]), OId("x")));
    private static Formula OContext(Formula body, bool twoMaps) =>
        OAll("E", OCall("Type"),
            Seq(OpenBracket, OCall("NormedAddCommGroup", OId("E")), CloseBracket, Sp,
                OpenBracket, OCall("InnerProductSpace", OType("Complex"), OId("E")), CloseBracket, Sp,
                OAll("n", OType("Nat"),
                    Seq(OpenBracket, OCall("FiniteDimensional", OType("Complex"), OId("E")), CloseBracket, Sp,
                        OAll("T", OLinearMap(), twoMaps ? OAll("S", OLinearMap(), body) : body)))));
    private static Formula OSpectralContext(Formula body) =>
        OAll("hT", OQualified("LinearMap", "IsSymmetric", OId("T")),
            OAll("hn", OEq(ORank(OId("E")), OId("n")),
                OAll("k", OCall("Fin", OId("n")), body)));
    private static Formula UnitVectorFormula() => OContext(OSpectralContext(
        OAll("V", OSubmodule(), OImp(OEq(ORank(OId("V")), ODimension()),
            OExists("x", OId("E"), OAnd(OMem(OId("x"), OId("V")),
                OAnd(OEq(new Formula.Norm(OId("x")), D(1)), OLe(ORayleigh(), OEigen("hT")))))))), false);
    private static Formula SubmoduleFormula() => OContext(OSpectralContext(
        OExists("V", OSubmodule(), OAnd(OEq(ORank(OId("V")), ODimension()),
            OAll("x", OId("E"), OImp(OMem(OId("x"), OId("V")),
                OImp(OEq(new Formula.Norm(OId("x")), D(1)), OLe(OEigen("hT"), ORayleigh()))))))), false);
    private static Formula PerturbationFormula()
    {
        Formula difference = new Formula.Binary(OId("T"), FormulaBinaryOperator.Subtract, OId("S"));
        Formula bound = OAll("x", OId("E"), OLe(new Formula.Norm(new Formula.Apply(Parenthesized(difference), [OId("x")])),
            new Formula.Binary(OId("epsilon"), FormulaBinaryOperator.Multiply, new Formula.Norm(OId("x")))));
        Formula conclusion = OAll("k", OCall("Fin", OId("n")),
            OLe(new Formula.Absolute(new Formula.Binary(OEigen("hT"), FormulaBinaryOperator.Subtract, OEigen("hS"))), OId("epsilon")));
        return OContext(OAll("hT", OQualified("LinearMap", "IsSymmetric", OId("T")),
            OAll("hS", OQualified("LinearMap", "IsSymmetric", OId("S")),
                OAll("hn", OEq(ORank(OId("E")), OId("n")),
                    OAll("epsilon", OType("Real"), OImp(bound, conclusion))))), true);
    }
}
