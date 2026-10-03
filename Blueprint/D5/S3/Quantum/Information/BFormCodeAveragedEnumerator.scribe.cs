using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class BFormCodeAveragedEnumeratorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/BFormCodeAveragedEnumerator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/angelinos2022narain");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime p, every c and every function t on Z/p with t(-a) = t(a), the full enumerator polynomial of the code with generating matrix (I | B^T), evaluated at x_ab = t_a t_b and averaged over the p^(c(c-1)/2) antisymmetric matrices B with zero diagonal, equals the cosine formula (barP) conjectured by N. Angelinos, D. Chakraborty and A. Dymarsky (arXiv:2206.14825).",
        H("The averaged enumerator of B-form codes"),
        Blocks(
            Node("bform", "B-form matrices", BFormFormula(),
                "A c x c matrix B over Z/p is of B-form when it is antisymmetric and has zero diagonal; the code it generates has generating matrix (I | B^T).",
                "IsBForm", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("enumerator", "The full enumerator at x_ab = t_a t_b", EnumeratorFormula(),
                "The codewords of the code of B are the pairs (r, B^T r) with r in (Z/p)^c. Its full enumerator is the sum over the codewords of the product over i of x_(r_i, (B^T r)_i); the paper evaluates it at x_ab = t_a t_b.",
                "enumerator", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured average", ClaimFormula(),
                "Eq. (barP) of the paper: the average of the enumerator over all B-form matrices, for every prime p, every c and every t with t(-a) = t(a). In the cosine, k, a and b are read as their representatives 0, ..., p - 1. In the exponent c(c - 1) is a natural number, natDiv is division of natural numbers rounded down and c - 1 is subtraction of natural numbers (0 at c = 0); c(c - 1) is even, so natDiv(c(c - 1), 2) = c(c - 1)/2 is the number of entries above the diagonal, and there are p^(c(c-1)/2) B-form matrices.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the averaged formula", Disp(F.Id("claim")),
                "Exchange the sums over B and r. The term r = 0 gives t_0^(2c) for every B. For r nonzero, antisymmetry with zero diagonal gives r . B^T r = 0, and the linear map B -> B^T r is onto the hyperplane orthogonal to r: if r_j is nonzero, a matrix supported on row and column j reaches any s orthogonal to r. So each such s has the same number of preimages, and the sum over B equals p^(c(c-1)/2) / p^(c-1) times the sum over s orthogonal to r. The constraint r . s = 0 is written as p^(-1) times the sum over k of the standard additive character psi(k r . s); the sum over r and s then factors into the c-th power of the sum over a and b of psi(kab) t_a t_b, and the row r = 0 contributes p t_0^c (sum of t_a)^c. Since t is even, replacing (a, b) by (-a, b) turns psi(kab) into its complex conjugate, so the character sum equals the cosine sum. Counting the B-form matrices as p^(c(c-1)/2) gives the formula.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("angelinos-2022-bform-averaged-enumerator"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("narain-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(F.Id(name)), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Sum, index), Sp, body);
    private static Formula ProdOver(Formula index, Formula body) =>
        Seq(new Formula.Subscript(Prod, index), Sp, body);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula ZModP() => Seq(Mathbb, Grp(F.Id("Z")), Slash, F.Id("p"));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vectors() => Pow(Parenthesized(ZModP()), F.Id("c"));
    private static Formula Matrices() => Call("Mat", F.Id("c"), ZModP());
    private static Formula Transposed(Formula matrix) => Pow(matrix, F.Id("T"));
    private static Formula T(Formula argument) => new Formula.Apply(F.Id("t"), [argument]);
    private static Formula Val(Formula value) => Call("val", value);

    private static Formula BFormFormula()
    {
        Formula B = F.Id("B"), i = F.Id("i");
        Formula antisymmetric = Equal(Transposed(B), new Formula.Negate(B));
        Formula diagonal = All("i", Call("Fin", F.Id("c")),
            Equal(new Formula.Subscript(B, Seq(i, i)), D(0)));
        return Disp(Iff(Call("IsBForm", B), And(antisymmetric, diagonal)));
    }

    private static Formula EnumeratorFormula()
    {
        Formula B = F.Id("B"), r = F.Id("r"), i = F.Id("i");
        Formula image = new Formula.Subscript(Parenthesized(Seq(Transposed(B), Sp, r)), i);
        Formula body = ProdOver(i, Mul(T(new Formula.Subscript(r, i)), T(image)));
        return Disp(Equal(Call("enumerator", F.Id("t"), B), SumOver(Member(r, Vectors()), body)));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("p"), c = F.Id("c"), t = F.Id("t"), B = F.Id("B");
        Formula k = F.Id("k"), a = F.Id("a"), b = F.Id("b");
        Formula average = Div(
            SumOver(Seq(Member(B, Matrices()), Comma, Sp, Call("IsBForm", B)), Call("enumerator", t, B)),
            Pow(p, Call("natDiv", Mul(c, Parenthesized(Sub(c, D(1)))), D(2))));
        Formula angle = Div(Mul(Mul(Mul(Seq(D(2), Pi), Val(k)), Val(a)), Val(b)), p);
        Formula cosineSum = SumOver(Member(a, ZModP()), SumOver(Member(b, ZModP()),
            Mul(Mul(Call("cos", angle), T(a)), T(b))));
        Formula powers = SumOver(Member(k, ZModP()), Pow(Parenthesized(cosineSum), c));
        Formula zeroRow = Mul(Mul(p, Pow(T(D(0)), c)),
            Pow(Parenthesized(SumOver(Member(a, ZModP()), T(a))), c));
        Formula formula = Add(Pow(T(D(0)), Mul(D(2), c)), Div(Sub(powers, zeroRow), Pow(p, c)));
        Formula even = All("a", ZModP(), Equal(T(new Formula.Negate(a)), T(a)));
        Formula body = Implies(even, Equal(average, formula));
        Formula quantified = All("p", Nats(), Implies(Call("Prime", p),
            All("c", Nats(), All("t", Seq(ZModP(), Sp, To, Sp, Complexes()), body))));
        return Disp(Iff(F.Id("claim"), quantified));
    }
}
