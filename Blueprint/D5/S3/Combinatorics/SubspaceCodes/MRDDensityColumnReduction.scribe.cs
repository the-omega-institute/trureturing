using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubspaceCodes;

internal sealed class MRDDensityColumnReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnReduction.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/gruica2023mrdcolumnlimit");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-field MRD density: reduction argument.", H("MRD density: Reduction"), Blocks(
            Node("gaussian", "Gaussian",
                All("q", Nat, All("a", Nat, All("b", Nat, Equal(Call("gaussian", X("q"), X("a"), X("b")), ProductOn("h", App(Q("Finset", "range"), X("b")), Div(Parenthesized(Subtract(Pow(Typed(X("q"), R), X("a")), Pow(Typed(X("q"), R), X("h")))), Parenthesized(Subtract(Pow(Typed(X("q"), R), X("b")), Pow(Typed(X("q"), R), X("h")))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1082 (arXiv v1): “Throughout the paper we will extensively use the q-binomial coefficient of non-negative integers i ≥ j, defined as”. The displayed finite product is that expression; all indices are natural numbers."),
            Node("P", "P",
                All("q", Nat, Equal(Call("P", X("q")), App(Word("tprod"), Lambda("j", Nat, Subtract(D(1), Pow(Inverse(Typed(X("q"), R)), Parenthesized(Add(X("j"), D(1))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                @"Page 1083: “Notice that \pi is closely related to the Euler function \phi, which is defined by \phi(x)=\prod_{i=1}^\infty (1-x^i) for x \in (-1,1). Indeed, we have \pi(q)=1/\phi(1/q).” Here P(q) = φ(1/q) = 1/π(q). The index j starts at zero, so the factor uses j+1."),
            Node("MinDistanceAtLeast", "Mindistanceatleast",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("d", Nat, All("C", Call("Submodule", X("K"), Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K"))), Equal(Call("MinDistanceAtLeast", X("K"), X("n"), X("m"), X("d"), X("C")), All("M", Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K")), Imp(Member(X("M"), X("C")), Imp(Ne(X("M"), D(0)), Leq(X("d"), App(Q("Matrix", "rank"), X("M")))))))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1081: “A (rank-metric) code is a non-zero \\F_q-subspace \\mC \\le \\mat. Its minimum distance is \\drk(\\mC)=\\min\\{\\rk(M) \\mid M \\in \\mC, \\; M \\neq 0\\}.” The predicate states the lower bound on every nonzero matrix in the subspace. K is the finite field carrier and n,m are the matrix dimensions."),
            Node("GoodCodes", "Goodcodes",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("k", Nat, All("d", Nat, Equal(Call("GoodCodes", X("K"), X("n"), X("m"), X("k"), X("d")), SubtypeOf("C", Call("Submodule", X("K"), Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K"))), And(Equal(App(Q("Module", "finrank"), X("K"), X("C")), X("k")), Call("MinDistanceAtLeast", X("K"), X("n"), X("m"), X("d"), X("C")))))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The numerator consists of the k-dimensional matrix subspaces satisfying the minimum-distance predicate."),
            Node("AllCodes", "Allcodes",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("k", Nat, Equal(Call("AllCodes", X("K"), X("n"), X("m"), X("k")), SubtypeOf("C", Call("Submodule", X("K"), Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K"))), Equal(App(Q("Module", "finrank"), X("K"), X("C")), X("k")))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The denominator consists of all k-dimensional matrix subspaces."),
            Node("density", "Density",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("k", Nat, All("d", Nat, Equal(Call("density", X("K"), X("n"), X("m"), X("k"), X("d")), Div(Typed(App(Q("Nat", "card"), Call("GoodCodes", X("K"), X("n"), X("m"), X("k"), X("d"))), R), Typed(App(Q("Nat", "card"), Call("AllCodes", X("K"), X("n"), X("m"), X("k"))), R)))))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1082, Notation 2.5: “This number measures the proportion of rank-metric codes with minimum distance at least d within the k-dimensional ones.” The displayed quotient uses the cardinality of those two collections, the source numerator and its Gaussian-binomial denominator."),
            Node("mrdDimension", "Mrddimension",
                All("n", Nat, All("m", Nat, All("d", Nat, Equal(Call("mrdDimension", X("n"), X("m"), X("d")), Mul(X("m"), Parenthesized(Add(Subtract(X("n"), X("d")), D(1)))))))),
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Page 1082: “Note that, by definition, the density function of MRD codes is given by” δʳᵏq(n×m,m(n−d+1),d). The dimension is m(n−d+1), with natural subtraction used under d ≤ n."),
            Node("limit_one", "Limit one",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("n", Nat, Imp(Leq(D(1), X("n")), App(Q("Filter", "Tendsto"), Lambda("m", Nat, Call("density", X("K"), X("n"), X("m"), Call("mrdDimension", X("n"), X("m"), D(1)), D(1))), Q("Filter", "atTop"), Call("nhds", D(1)))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The full-dimensional code is unique, and every nonzero matrix has rank at least one. Thus the density for distance one is one and has the indicated limit."),
            Node("product_limit", "Product limit",
                All("q", Nat, Imp(Leq(D(2), X("q")), App(Q("Filter", "Tendsto"), Lambda("k", Nat, ProductOn("j", App(Q("Finset", "range"), X("k")), Parenthesized(Subtract(D(1), Pow(Inverse(Typed(X("q"), R)), Parenthesized(Add(X("j"), D(1)))))))), Q("Filter", "atTop"), Call("nhds", Call("P", X("q")))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The finite products converge to the infinite product for every integer q at least two."),
            Node("subspace_of_dimension_le", "Subspace of dimension le",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, All("E", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("E")), CloseBracket, Sp, Seq(OpenBracket, Call("FiniteDimensional", X("K"), X("E")), CloseBracket, Sp, All("W", Call("Submodule", X("K"), X("E")), All("r", Nat, Imp(Leq(X("r"), App(Q("Module", "finrank"), X("K"), X("W"))), Some("U", Call("Submodule", X("K"), X("E")), And(Equal(App(Q("Module", "finrank"), X("K"), X("U")), X("r")), Leq(X("U"), X("W"))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "A subspace contains a subspace of every dimension up to its own dimension."),
            Node("restrictRows", "Restrictrows",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("U", Call("Submodule", X("K"), Arrow(Call("Fin", X("n")), X("K"))), All("M", Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K")), Equal(Call("restrictRows", X("n"), X("m"), X("U"), X("M")), App(Q("LinearMap", "comp"), App(Seq(Q("Matrix", "toLin"), Apos), App(Q("Matrix", "transpose"), X("M"))), App(Q("Submodule", "subtype"), X("U")))))))))),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "The map sends a matrix to the linear map of its transposed rows, restricted to the given subspace. The displayed expression specifies its value on every matrix; its linearity follows from linearity of composition."),
            Node("mrd_iff_restrictions_injective", "Mrd iff restrictions injective",
                All("K", Word("Type"), Seq(OpenBracket, Call("Field", X("K")), CloseBracket, Sp, Seq(OpenBracket, Call("Fintype", X("K")), CloseBracket, Sp, All("D", Word("Type"), Seq(OpenBracket, Call("AddCommGroup", X("D")), CloseBracket, Sp, Seq(OpenBracket, Call("Module", X("K"), X("D")), CloseBracket, Sp, All("n", Nat, All("m", Nat, All("d", Nat, Imp(Leq(X("d"), X("n")), All("f", Call("LinearMap", App(Q("RingHom", "id"), X("K")),  X("D"), Call("Matrix", Call("Fin", X("n")), Call("Fin", X("m")), X("K"))), Imp(App(Q("Function", "Injective"), X("f")), IffOf(Call("MinDistanceAtLeast", X("K"), X("n"), X("m"), X("d"), App(Q("LinearMap", "range"), X("f"))), All("U", Call("Submodule", X("K"), Arrow(Call("Fin", X("n")), X("K"))), Imp(Equal(App(Q("Module", "finrank"), X("K"), X("U")), Add(Subtract(X("n"), X("d")), D(1))), App(Q("Function", "Injective"), App(Q("LinearMap", "comp"), Call("restrictRows", X("n"), X("m"), X("U")), X("f")))))))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "For an injective generator, the rank-distance condition is equivalent to injectivity of all restrictions along subspaces of dimension n−d+1."),
            Node("mixed_mobius_error", "Mixed mobius error",
                All("I", Word("Type"), Seq(OpenBracket, Call("DecidableEq", X("I")), CloseBracket, Sp, All("s", Call("Finset", X("I")), All("q", R, Imp(Leq(D(0), X("q")), All("t", Arrow(X("I"), Nat), All("R", Nat, Leq(Abs(Subtract(Parenthesized(ProductOn("i", X("s"), Parenthesized(SumOn("k", App(Q("Finset", "range"), Add(X("R"), D(1))), Mul(Mul(Pow(Parenthesized(Negate(D(1))), X("k")), Pow(X("q"), App(Q("Nat", "choose"), X("k"), D(2)))), Call("gaussValue", X("q"), App(X("t"), X("i")), X("k"))))))), Parenthesized(ProductOn("i", X("s"), Parenthesized(IfThenElse(Equal(App(X("t"), X("i")), D(0)), D(1), D(0))))))), Subtract(ProductOn("i", X("s"), Parenthesized(Add(D(1), Mul(Pow(X("q"), App(Q("Nat", "choose"), Add(X("R"), D(1)), D(2))), Call("gaussValue", X("q"), App(X("t"), X("i")), Add(X("R"), D(1))))))), D(1)))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The error of the product of truncated Gaussian Möbius sums is controlled by the product of their nonnegative individual errors."),
            Node("gaussian_eq_polynomial", "Gaussian eq polynomial",
                All("q", Nat, All("a", Nat, All("b", Nat, Imp(Leq(D(2), X("q")), Imp(Leq(X("b"), X("a")), Equal(Call("gaussian", X("q"), X("a"), X("b")), Call("gaussValue", Typed(X("q"), R), X("a"), X("b")))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "For in-range indices over a finite field cardinality at least two, the finite-product Gaussian coefficient equals evaluation of the integer Gaussian polynomial."),
            Node("approximating_limits", "Approximating limits",
                All("p", Arrow(Nat, R), All("a", Arrow(Nat, Arrow(Nat, R)), All("b", Arrow(Nat, Arrow(Nat, R)), All("c", Arrow(Nat, R), All("e", Arrow(Nat, R), All("L", R, Imp(All("R", Nat, App(Q("Filter", "Eventually"), Lambda("m", Nat, Leq(Abs(Subtract(App(X("p"), X("m")), App(X("a"), X("R"), X("m")))), App(X("b"), X("R"), X("m")))), Q("Filter", "atTop"))), Imp(All("R", Nat, App(Q("Filter", "Tendsto"), App(X("a"), X("R")), Q("Filter", "atTop"), Call("nhds", App(X("c"), X("R"))))), Imp(All("R", Nat, App(Q("Filter", "Tendsto"), App(X("b"), X("R")), Q("Filter", "atTop"), Call("nhds", App(X("e"), X("R"))))), Imp(App(Q("Filter", "Tendsto"), X("c"), Q("Filter", "atTop"), Call("nhds", X("L"))), Imp(App(Q("Filter", "Tendsto"), X("e"), Q("Filter", "atTop"), Call("nhds", D(0))), App(Q("Filter", "Tendsto"), X("p"), Q("Filter", "atTop"), Call("nhds", X("L")))))))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "Limits of approximants determine the limit of a sequence when the limiting error tends to zero."),
            Node("vanishing_nondirect", "Vanishing nondirect",
                All("q", R, Imp(Less(D(1), X("q")), All("C", R, All("w", Arrow(Nat, R), Imp(App(Q("Filter", "Eventually"), Lambda("m", Nat, Leq(D(0), App(X("w"), X("m")))), Q("Filter", "atTop")), Imp(App(Q("Filter", "Eventually"), Lambda("m", Nat, Leq(App(X("w"), X("m")), Mul(X("C"), Inverse(Pow(X("q"), X("m")))))), Q("Filter", "atTop")), App(Q("Filter", "Tendsto"), X("w"), Q("Filter", "atTop"), Call("nhds", D(0))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "A nonnegative sequence bounded eventually by a fixed constant times q to the negative column count tends to zero when q exceeds one."),
            Node("automorphismProduct", "Automorphismproduct",
                All("q", R, All("k", Nat, Equal(Call("automorphismProduct", X("q"), X("k")), ProductOn("h", App(Q("Finset", "range"), X("k")), Parenthesized(Subtract(Pow(X("q"), X("k")), Pow(X("q"), X("h")))))))),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "The product of qᵏ−qʰ over h from zero to k−1 is the cardinality of the general linear group when q is a finite field cardinality."),
            Node("automorphism_product_lower", "Automorphism product lower",
                All("q", R, Imp(Leq(D(2), X("q")), All("k", Nat, Leq(Pow(X("q"), Parenthesized(Mul(X("k"), Parenthesized(Subtract(X("k"), D(1)))))), Call("automorphismProduct", X("q"), X("k")))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "Each factor of the general linear group product is at least qᵏ⁻¹ when q is at least two."),
            Node("mobius_tail_bound", "Mobius tail bound",
                All("q", R, Imp(Leq(D(2), X("q")), All("R", Nat, And(Leq(D(0), Div(Pow(X("q"), App(Q("Nat", "choose"), Add(X("R"), D(1)), D(2))), Call("automorphismProduct", X("q"), Add(X("R"), D(1))))), Leq(Div(Pow(X("q"), App(Q("Nat", "choose"), Add(X("R"), D(1)), D(2))), Call("automorphismProduct", X("q"), Add(X("R"), D(1)))), Inverse(Pow(X("q"), X("R")))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The normalized first omitted Möbius coefficient is nonnegative and at most q to the negative truncation order."),
            Node("mobius_tail_limit", "Mobius tail limit",
                All("q", R, Imp(Leq(D(2), X("q")), App(Q("Filter", "Tendsto"), Lambda("R", Nat, Div(Pow(X("q"), App(Q("Nat", "choose"), Add(X("R"), D(1)), D(2))), Call("automorphismProduct", X("q"), Add(X("R"), D(1))))), Q("Filter", "atTop"), Call("nhds", D(0))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The omitted Möbius coefficient divided by the general linear group product tends to zero."),
            Node("gaussian_symmetry", "Gaussian symmetry",
                All("q", Nat, All("n", Nat, All("k", Nat, Imp(Leq(D(2), X("q")), Imp(Leq(X("k"), X("n")), Equal(Call("gaussian", X("q"), X("n"), X("k")), Call("gaussian", X("q"), X("n"), Parenthesized(Subtract(X("n"), X("k")))))))))),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The finite-product Gaussian coefficient is unchanged by replacing the subspace dimension by its codimension."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("mrd-reduction-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula X(string name) => F.Id(name);
    private static Formula Word(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula Q(string owner, string name) => Seq(Word(owner), Dot, Word(name));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Some(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula SumOn(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(X(name), InMacro, Sp, domain)), Sp, body);
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula IfThenElse(Formula condition, Formula a, Formula b) => Parenthesized(Seq(Word("if"), Sp, condition, Sp, Word("then"), Sp, a, Sp, Word("else"), Sp, b));
    private static Formula Negate(Formula a) => new Formula.Negate(a);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Inverse(Formula a) => new Formula.Power(a, Seq(Minus, D(1)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(Word("fun"), Sp, X(name), Colon, type, Sp, Mapsto, Sp, body));
    private static Formula ProductOn(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Prod, Seq(X(name), InMacro, Sp, domain)), Sp, body);
    private static Formula SubtypeOf(string name, Formula type, Formula body) => Seq(OpenBrace, X(name), Colon, type, Sp, Slash, Slash, Sp, body, CloseBrace);

}
