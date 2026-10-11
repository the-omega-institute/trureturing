using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class TernaryTranslationQuadraticNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translation on a ternary group pairs opposite Fourier modes. A symmetric binary quadratic form consequently decomposes into bilinear blocks over ℤ/2ℤ.",
        H("Bilinear coordinates for a ternary translation form"),
        Blocks(
            Entry("quadratic-form", "F", "The translation quadratic form", TranslationForm(),
                "The variables are binary configurations indexed by the group Fin d → ℤ/3ℤ. For each ordered edge u < v, the form adds the original edge product to the product translated separately by δ(u) and δ(v). All sums and products in this definition take values in ℤ/2ℤ.",
                DescribeRole.Definition),
            Entry("separation-matrix", "C", "The character separation matrix", SeparationMatrix(),
                "The matrix keeps A(u,v) when the two ternary dot products differ and sets the entry to zero when they agree. Thus a character measures the separation of the two translation vectors.",
                DescribeRole.Definition),
            Entry("bilinear-coordinates", "ternary_translation_quadratic_normal_form", "A linear equivalence to independent blocks", NormalForm(),
                "Assume that A is symmetric and that P contains exactly one element from every opposite pair of nonzero modes. The ℤ/2ℤ-linear equivalence E has one constant-mode vector and a pair of binary vectors for each representative. The displayed sum uses precisely the first and second vectors of that pair. Fourier inversion over ℤ/2ℤ[ω], where ω² + ω + 1 = 0, constructs the equivalence; opposite modes are conjugate, and their cross terms give the bilinear blocks C(A,δ,t). No condition on the diagonal of A is required.",
                DescribeRole.Theorem))));

    private static Formula TranslationForm() => Dimensions(
        All(V("A"), BinaryMatrix, All(DeltaLower, Translations, All(V("x"), Configurations,
            Equal(Call("F", V("A"), DeltaLower, V("x")),
                SumOver(Typed(V("r"), Group), SumOver(Typed(V("u"), Fin(V("N"))), SumOver(Typed(V("v"), Fin(V("N"))),
                    Call("ite", Seq(V("u"), Sp, Lt, Sp, V("v")),
                        Multiply(Call("A", V("u"), V("v")), Parenthesized(Seq(
                            Multiply(Call("x", V("r"), V("u")), Call("x", V("r"), V("v"))), Sp, Plus, Sp,
                            Multiply(Call("x", Parenthesized(Seq(V("r"), Sp, Plus, Sp, Apply(DeltaLower, V("u")))), V("u")),
                                Call("x", Parenthesized(Seq(V("r"), Sp, Plus, Sp, Apply(DeltaLower, V("v")))), V("v")))))), D(0))))))))));

    private static Formula SeparationMatrix() => Dimensions(
        All(V("A"), BinaryMatrix, All(DeltaLower, Translations, All(V("t"), Group,
            Equal(Call("C", V("A"), DeltaLower, V("t")),
                Seq(Typed(V("u"), Fin(V("N"))), Sp, Typed(V("v"), Fin(V("N"))), Sp, Mapsto, Sp,
                    Call("ite", Equal(DotTranslation(V("u")), DotTranslation(V("v"))), D(0), Call("A", V("u"), V("v")))))))));

    private static Formula NormalForm()
    {
        var symmetry = All(V("u"), Fin(V("N")), All(V("v"), Fin(V("N")),
            Equal(Call("A", V("u"), V("v")), Call("A", V("v"), V("u")))));
        var representatives = All(V("t"), Group, Imp(Seq(V("t"), Sp, Neq, Sp, D(0)),
            Parenthesized(Seq(Member(V("t"), V("P")), Sp, Leftrightarrow, Sp,
                Not(Member(Seq(Minus, V("t")), V("P")))))));
        var blocks = SumOver(Typed(V("t"), Representatives),
            SumOver(Typed(V("u"), Fin(V("N"))), SumOver(Typed(V("v"), Fin(V("N"))),
                Multiply(Multiply(Coordinate(D(1), V("u")),
                    Apply(Call("C", V("A"), DeltaLower, Property(V("t"), "val")), V("u"), V("v"))),
                    Coordinate(D(2), V("v"))))));
        var codomain = Parenthesized(Seq(Vector, Sp, Times, Sp,
            Arrow(Representatives, Parenthesized(Seq(Vector, Sp, Times, Sp, Vector)))));
        var equivalence = Some(V("E"), LinearEquivalence(Configurations, codomain),
            All(V("x"), Configurations, Equal(Call("F", V("A"), DeltaLower, V("x")), blocks)));
        return Dimensions(All(V("A"), BinaryMatrix, Imp(Parenthesized(symmetry),
            All(DeltaLower, Translations, All(V("P"), Call("Finset", Group),
                Imp(Not(Member(D(0), V("P"))), Imp(Parenthesized(representatives), equivalence)))))));
    }

    private static Formula Coordinate(Formula side, Formula index) => Apply(
        Projection(Apply(Projection(Call("E", V("x")), D(2)), V("t")), side), index);
    private static Formula DotTranslation(Formula qubit) => SumOver(Typed(V("i"), Fin(V("d"))),
        Multiply(Call("t", V("i")), Apply(DeltaLower, qubit, V("i"))));
    private static Formula Dimensions(Formula body) => All(V("N"), Nat, All(V("d"), Nat, body));
    private static Formula Group => Arrow(Fin(V("d")), Call("ZMod", D(3)));
    private static Formula Vector => Arrow(Fin(V("N")), Binary);
    private static Formula Configurations => Arrow(Group, Vector);
    private static Formula Translations => Arrow(Fin(V("N")), Group);
    private static Formula BinaryMatrix => Call("Matrix", Fin(V("N")), Fin(V("N")), Binary);
    private static Formula Representatives => Seq(OpenBrace, Typed(V("t"), Group), Sp, Mid, Sp, Member(V("t"), V("P")), CloseBrace);
    private static Formula LinearEquivalence(Formula a, Formula b) => Call("LinearEquiv", Binary, a, b);

    private static DocumentBlock Entry(string id, string declaration, string title, Formula statement,
        string explanation, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Binary => Call("ZMod", D(2));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula name, Formula type) => Parenthesized(Seq(name, Sp, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Not(Formula x) => Seq(Neg, Sp, Parenthesized(x));
    private static Formula Multiply(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula SumOver(Formula i, Formula x) => Seq(Sum, Underscore, Grp(i), Sp, x);
    private static Formula Projection(Formula x, Formula i) => Seq(Parenthesized(x), Dot, i);
    private static Formula Property(Formula x, string property) => Seq(Parenthesized(x), Dot, V(property));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => Seq(f, Open, Arguments(args), Close);
    private static Formula Arguments(Formula[] args) => Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x })]);
}
