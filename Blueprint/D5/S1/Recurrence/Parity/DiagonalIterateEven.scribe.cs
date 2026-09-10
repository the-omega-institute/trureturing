using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DiagonalIterateEvenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DiagonalIterateEven.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a395842");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The implicitly determined compositional series has even diagonal coefficients at every index at least two.",
        H("Even Diagonal Coefficients of Compositional Iterates"),
        Blocks(
            Paragraph(Text("OEIS A395842 conjectures that every term after the initial term is even. "
                + "Here iterate(f,0)=X and iterate(f,m+1) substitutes f into iterate(f,m). "
                + "The imported iterate definition is used throughout; iteration is composition. "
                + "All indices are natural numbers, and subtraction of indices is truncated at zero. "
                + "Coefficients and divisibility in the final theorem are over the integers.")),
            Node("generatingSeries", "Construction of the integer series",
                Disp(Equal(G(), Call("limitSeries", Integers()))),
                "The auxiliary approximation starts with X+X². At stage j it subtracts "
                + "the degree-(j+3) diagonal residual times X^(j+3). Coefficients below "
                + "that degree are preserved. limitSeries is mk applied to the function "
                + "n mapped to coeff(n,approximation(n)); mk constructs a power series "
                + "from its coefficients. No parity constraint enters this construction.",
                DescribeRole.Definition),
            Node("a", "The diagonal sequence",
                Disp(Seq(Bound("n", Naturals()), Equal(Call("a", N()), Coeff(N(), Iter(G(), N()))))),
                "The integer a(n) is exactly the degree-n coefficient of the n-th "
                + "iterate of the constructed series. The normalization implies a(2)=2.",
                DescribeRole.Definition),
            Node("generating_equation", "The defining diagonal constraints",
                Disp(Specification(G())),
                "For normalized series agreeing below degree n, the change in the "
                + "degree-n coefficient of the m-th iterate is m times the change in "
                + "the degree-n coefficient of the series. Subtracting adjacent iterates "
                + "therefore leaves that coefficient change once. Each correction kills "
                + "its residual, and coefficient stability transfers every constraint to the limit."),
            Node("generating_unique", "Uniqueness",
                Disp(Seq(Bound("f", Call("PowerSeries", Integers())),
                    Implication(Specification(F.Id("f")), Equal(F.Id("f"), G())))),
                "Strong induction compares coefficients of two solutions. Degrees zero, "
                + "one and two are prescribed. At every later degree, equality of the "
                + "lower coefficients and vanishing residuals force equality of the next coefficient."),
            Node("hanna_conjecture", "Every diagonal coefficient from index two is even",
                Disp(Seq(Bound("n", Naturals()), Implication(Seq(D(2), Sp, Le, Sp, N()),
                    Seq(D(2), Sp, Mid, Sp, Call("a", N()))))),
                "Over ZMod(2), take H to be the compositional inverse of X+X². It satisfies "
                + "H+H²=X. Doubling an iterate proves U+U^(2^(2^r))=X for U=iterate(H,2^r), "
                + "so its coefficients from degree two through 2^(2^r)-1 vanish. "
                + "The relation iterate(H,m+1)+iterate(H,m+1)²=iterate(H,m), together with "
                + "Frobenius substitution, excludes every degree that is not a power of two "
                + "by induction on degree and iteration count. These facts prove the diagonal "
                + "constraints and vanishing diagonal for H. Reduction of the integer solution "
                + "commutes with iteration; uniqueness identifies it with H. Its zero diagonal "
                + "coefficients in ZMod(2) are exactly integer divisibility by two."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("diagonal-iterate-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula N() => F.Id("n");
    private static Formula G() => Call("generatingSeries");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Iter(Formula f, Formula n) => Call("iterate", Integers(), f, n);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Parens(Formula f) => Seq(Open, f, Close);
    private static Formula Implication(Formula premise, Formula result) =>
        Seq(Parens(premise), Sp, Implies, Sp, result);
    private static Formula Specification(Formula f) => Seq(
        Parens(Equal(Call("constantCoeff", f), D(0))), Sp, Land, Sp,
        Parens(Equal(Coeff(D(1), f), D(1))), Sp, Land, Sp,
        Parens(Equal(Coeff(D(2), f), D(1))), Sp, Land, Sp,
        Parens(Seq(Bound("n", Naturals()), Implication(Seq(D(2), Sp, Lt, Sp, N()),
            Equal(Coeff(N(), Iter(f, N())), Coeff(N(), Iter(f,
                new Formula.Binary(N(), FormulaBinaryOperator.Subtract, D(1)))))))));
}
