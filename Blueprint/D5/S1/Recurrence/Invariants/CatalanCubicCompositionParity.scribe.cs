using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CatalanCubicCompositionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CatalanCubicCompositionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2023a363308");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of C(x*C(x)^3) are odd exactly at zero and powers of two.",
        H("Hanna's Cubic Catalan Composition"),
        Blocks(
            Paragraph(Text("The generating function and parity conjecture are recorded "
                + "in hanna2023a363308. Write C for catalanSeries and A for generatingSeries. "
                + "Both series have integer coefficients, and X is the indeterminate. "
                + "All coefficient indices and exponents are natural numbers. "
                + "The operator subst(f,u) denotes formal composition f(u).")),
            Paragraph(Text("The operator mk forms a series from its coefficient function, "
                + "catalan is Mathlib's natural Catalan sequence, and natCast denotes "
                + "the coercion from natural numbers to integers. Write K for "
                + "CatalanCompositionSquareParity.catalanSeries, the integer series XC. "
                + "The operator map applies a ring homomorphism to every coefficient; "
                + "intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)).")),
            Node("catalanSeries", "The Catalan generating series", CatalanDefinition(),
                "The degree-n coefficient is the integer cast of catalan(n).",
                DescribeRole.Definition),
            Node("catalan_equation", "The Catalan equation",
                Disp(Equal(Catalan(), Add(D(1), Mul(X(), Power(Catalan(), D(2)))))),
                "Map Mathlib's Catalan generating-series identity from natural "
                + "coefficients to integer coefficients."),
            Node("generatingSeries", "The cubic composition",
                Disp(Equal(A(), Call("subst", Catalan(), Argument()))),
                "Compose C with X times C cubed, exactly as in the generating function "
                + "in hanna2023a363308. The inner series has zero constant coefficient.",
                DescribeRole.Definition),
            Node("a", "The coefficient sequence",
                Disp(Seq(Bound("n"), Equal(Call("a", N()), Call("coeff", N(), A())))),
                "The integer a(n) is the degree-n coefficient of the composition A.",
                DescribeRole.Definition),
            Node("generating_equation", "The composition equation and constant term",
                Disp(Conjunction(Equal(Call("constantCoeff", A()), D(1)),
                    Equal(A(), Add(D(1), Mul(Parenthesized(Argument()), Power(A(), D(2))))))),
                "Substitution into the Catalan equation preserves addition, "
                + "multiplication, and powers. Taking constant coefficients gives one."),
            Node("mod_two_identity", "Reduction to the binary Catalan series",
                Disp(Equal(Reduce(A()), Add(D(1), Reduce(K())))),
                "Over ZMod(2), put c=map(intCast(ZMod(2)),C), k=map(intCast(ZMod(2)),K), "
                + "and y=X times c cubed. Then k=Xc and k(1+k)=X. Multiplying y times (1+k) squared "
                + "by X squared gives k cubed times (1+k) squared, which equals "
                + "k times (k(1+k)) squared, hence X squared times k. Cancel X squared. "
                + "Thus 1+k solves F=1+yF squared. Two solutions differ by an element "
                + "annihilated by 1-y(F+G); this factor has constant coefficient one "
                + "and is a unit. Uniqueness identifies the reduction of A with 1+k."),
            Node("hanna_conjecture", "The A363308 parity conjecture", Conjecture(),
                "The constant coefficient is one. At every positive index the "
                + "modulo-two identity reduces parity to binary_catalan from "
                + "CatalanCompositionSquareParity, which gives coefficient one "
                + "exactly at powers of two.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a363308-catalan-cubic-composition-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a363308-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula X() => F.Id("X");
    private static Formula Catalan() => F.Id("C");
    private static Formula A() => F.Id("A");
    private static Formula K() => F.Id("K");
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, Naturals(), Comma, Sp);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Argument() => Mul(X(), Power(Catalan(), D(3)));
    private static Formula Reduce(Formula f) =>
        Call("map", Call("intCast", Call("ZMod", D(2))), f);

    private static Formula CatalanDefinition() => Disp(Equal(Catalan(), Call("mk",
        Parenthesized(Seq(N(), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Call("natCast", Call("catalan", N())))))));

    private static Formula Conjecture() => Disp(Seq(Bound("n"),
        Call("Odd", Call("a", N())), Sp, Iff, Sp,
        Parenthesized(Seq(Equal(N(), D(0)), Sp, Lor, Sp,
            Parenthesized(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
                Equal(N(), Power(D(2), F.Id("k")))))))));
}
