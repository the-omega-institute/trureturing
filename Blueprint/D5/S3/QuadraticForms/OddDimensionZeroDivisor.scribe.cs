using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OddDimensionZeroDivisorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/OddDimensionZeroDivisor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bilinear map whose target has dimension at most that of its first factor and whose second factor has rank at least two has a zero divisor, provided every polynomial whose degree is the dimension of the first factor has a root whenever the two dimensions are equal; over the real numbers this holds in every odd dimension.",
        H("Zero divisors of bilinear maps"),
        Blocks(
            Node("zero-divisor", "exists_zero_divisor",
                "Zero divisors of bilinear maps",
                StatementSource.FromAuthor(ZeroDivisorFormula()),
                "Let K be a field, U, V, W vector spaces over K with W finite-dimensional, and m a K-bilinear map, written as a linear map from U to the linear maps from V to W. Suppose that dim W <= dim U, that the rank of V is greater than 1, and that, when dim W = dim U, every polynomial f over K of degree dim U has a root x in K. Then there are a nonzero a in U and a nonzero b in V with m(a, b) = 0. Here dim is finrank over K, which is 0 for an infinite-dimensional space, while rank(K, V) is the cardinal dimension of V, so V may be infinite-dimensional. "
                    + "Proof. If dim U were 0, then dim W = 0 = dim U and the constant polynomial 1, of degree 0, would need a root; so dim U is positive and U is finite-dimensional. Since the rank of V exceeds 1, there are linearly independent b and c in V. If the linear map a -> m(a, b) is not injective, a nonzero element of its kernel together with b is a zero divisor. Otherwise it is injective from U to W with dim W <= dim U, hence an isomorphism e, and dim W = dim U. The endomorphism e^(-1) composed with a -> m(a, c) has a characteristic polynomial of degree dim U, which has a root mu by hypothesis; an eigenvector a for mu satisfies m(a, c) = mu m(a, b), so m(a, c - mu b) = 0, and c - mu b is nonzero because b and c are independent. "
                    + "Over the real numbers every polynomial of odd degree has a root, so the conclusion holds whenever dim U is odd; in particular every bilinear multiplication on R^n with n odd and n >= 3 has zero divisors. The case U = V = W = R^3 follows by applying the theorem with the root condition supplied by the odd-degree root theorem of real closed fields; this specialization is not stated as a separate theorem here. Over an algebraically closed field the root condition holds in every positive dimension.",
                DescribeRole.Theorem,
                "Each hypothesis is needed; none of the following examples is formalized. The root condition: multiplication in the field Q(2^(1/3)), viewed as a bilinear map on Q^3, has no zero divisors, and the polynomial x^3 - 2 of degree 3 has no rational root; multiplication of complex numbers, viewed as a bilinear map on R^2, has no zero divisors, and x^2 + 1 has no real root. In both cases dim W = dim U, which is the only case in which the root condition is required. The bound dim W <= dim U: the tensor product map from R^3 x R^3 to R^3 tensor R^3, a space of dimension 9, has no zero divisors. The bound on the rank of V: scalar multiplication R^3 x R -> R^3 has no zero divisors. Finite dimension of W: composing the tensor product map with an embedding of R^9 into an infinite-dimensional space W gives finrank W = 0, so the dimension bound holds and the root condition is not required, but there is still no zero divisor. "
                    + "The theorem holds over an arbitrary field with three possibly different spaces and its proof does not use the theory of real division algebras. Only its real case U = V = W, which says that for odd n >= 3 no bilinear multiplication on R^n is free of zero divisors, is consistent with the classical results on real division algebras: by a theorem of H. Hopf, a finite-dimensional real division algebra has dimension a power of two, and by the work of Bott, Milnor and Kervaire its dimension is 1, 2, 4 or 8."))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement, string prose, DescribeRole role,
        params string[] more) =>
        Describe.Lean(DescribeId.Create("odd-dimension-zero-divisor-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(prose)), .. more.Select(paragraph => Paragraph(Text(paragraph)))]), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula Implies(Formula x, Formula y) => Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(n => new Formula.BoundVariable(FormulaIdentifier.Create(n), domain))], body);
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Inst(Formula c) => Seq(OpenBracket, c, CloseBracket);
    private static Formula Finrank(Formula k, Formula space) => Call("finrank", k, space);

    private static Formula ZeroDivisorFormula()
    {
        Formula k = F.Id("K"), u = F.Id("U"), v = F.Id("V"), w = F.Id("W");
        Formula m = F.Id("m"), f = F.Id("f"), x = F.Id("x"), a = F.Id("a"), b = F.Id("b");
        Formula rootCondition = Implies(Equal(Finrank(k, w), Finrank(k, u)),
            ForAll("f", Call("Polynomial", k),
                Implies(Equal(Call("natDegree", f), Finrank(k, u)),
                    Exists("x", k, Call("IsRoot", f, x)))));
        Formula conclusion = Exists("a", u, Exists("b", v,
            And(Rel(a, FormulaRelationOperator.NotEqual, D(0)),
                And(Rel(b, FormulaRelationOperator.NotEqual, D(0)),
                    Equal(Call("m", a, b), D(0))))));
        Formula body = ForAll("m", Call("LinearMap", k, u, Call("LinearMap", k, v, w)),
            Implies(rootCondition,
                Implies(Rel(Finrank(k, w), FormulaRelationOperator.LessThanOrEqual, Finrank(k, u)),
                    Implies(Rel(D(1), FormulaRelationOperator.LessThan, Call("rank", k, v)),
                        conclusion))));
        return Disp(ForAllMany(TypeStar, Seq(
            Inst(Call("Field", k)), Sp,
            Inst(Call("AddCommGroup", u)), Sp, Inst(Call("Module", k, u)), Sp,
            Inst(Call("AddCommGroup", v)), Sp, Inst(Call("Module", k, v)), Sp,
            Inst(Call("AddCommGroup", w)), Sp, Inst(Call("Module", k, w)), Sp,
            Inst(Call("FiniteDimensional", k, w)), Sp, body), "K", "U", "V", "W"));
    }
}
