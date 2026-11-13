using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class DiagonalIterateEvenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/DiagonalIterateEven.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a395842");
    private static readonly LibraryNoteRef ParitySource =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2026a177775");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized compositional series has odd ordinary coefficients exactly at powers of two, and even diagonal coefficients from index two.",
        H("Ordinary and Diagonal Coefficients of Compositional Iterates"),
        Blocks(
            Paragraph(Text("OEIS A395842 conjectures that every term after the initial term is even. "
                + "Here iterate(f,0)=X and iterate(f,m+1) substitutes f into iterate(f,m). "
                + "The imported iterate definition is used throughout; iteration is composition. "
                + "All indices are natural numbers, and subtraction of indices is truncated at zero. "
                + "Coefficients and divisibility in the final theorem are over the integers.")),
            Paragraph(Text("OEIS A177775 is the ordinary coefficient sequence of the same "
                + "generatingSeries G. The initial values are G(0)=0 and coeff(1,G)=coeff(2,G)=1; "
                + "they are specified by the original recursive program and by the revised "
                + "seed [0,1,1]. The NAME's adjacent-iterate condition holds for every n>2. "
                + "The construction and uniqueness below identify this normalized source "
                + "without assuming existence or integrality. Its ordinary coefficients "
                + "are coeff(n,G); a(n) below denotes the different diagonal sequence A395842. "
                + "The second OEIS offset component 3 adds no initial condition. "
                + "The A177775 conclusion includes every n≥1, both implications, and n=1=2^0. "
                + "The PARI programs themselves are not formalized.")),
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
                + "coefficients in ZMod(2) are exactly integer divisibility by two."),
            Node("result", "The full A177775 ordinary-coefficient parity characterization",
                Disp(Seq(Bound("n", Naturals()), Implication(Seq(D(1), Sp, Le, Sp, N()),
                    Parens(Seq(Call("Odd", Coeff(N(), G())), Sp, Iff, Sp,
                        Parens(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
                            Equal(N(), new Formula.Power(D(2), F.Id("k")))))))))),
                "Let P be CubicFifteenSubstitutionParity.powerTwoSeries over ZMod(2). "
                + "Its coefficient at n is the indicator of existence of a natural k with n=2^k. "
                + "The first component of thue_series_equation and characteristic two give "
                + "P+P²=X. The existing H satisfies H+H²=X, and both constant coefficients "
                + "are zero. CubicFifteenSubstitutionParity.quadratic_unique therefore gives "
                + "H=P. The existing mod_two_identity identifies the coefficientwise reduction "
                + "of G with H. Applying coeff(n) and ZMod.intCast_eq_one_iff_odd proves "
                + "the displayed equivalence in both directions for every positive n. "
                + "The zeroth exponent k=0 supplies n=1. This uses ordinary integer coefficients "
                + "of G and imposes no parity assumption on its construction.",
                provenance: AssessedProvenance.FromRepo(ParitySource)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("diagonal-iterate-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

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
