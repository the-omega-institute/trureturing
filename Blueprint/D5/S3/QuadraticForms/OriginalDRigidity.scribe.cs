using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class OriginalDRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common two-label Hermitian boundary forces scalar skew symmetry of the old response relation.",
        H("The first rigidity boundary for the original relation"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-label-skew"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/OriginalDRigidity.three_label_skew"),
            H("Hermitian response tables force skew symmetry"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("E is an arbitrary real module. S is the fixed real-bilinear symmetric part, D is still an arbitrary total relation, and alpha is one real-linear separating evaluation. ThreeLabelPSD requires the same response matrix to be positive semidefinite for every label list of order at most three, including zero, repeated and singular lists.")),
                Paragraph(Text("The response entry is alpha(S a b) minus i times alpha(D a b). Positive semidefinite matrices are Hermitian, so the two off-diagonal entries are conjugates. Since the S contribution is real and symmetric, their imaginary parts give alpha(D b a) = -alpha(D a b), including the diagonal zero case. No mass, Gram determinant, finite-dimensionality or regularity assumption is introduced.")),
                Paragraph(Text("The complete C128 source theorem additionally quantifies every original separating evaluation over the same old vector-valued D, assumes the common tables for every order from one through three and every zero, repeated, scaled and translated label list, and concludes alternating real-bilinearity of D together with all finite positive semidefiniteness of each scalar kernel. Those fixed-background, separation, singular-case and all-finite clauses remain the source context and target boundary for the unfinished cross-plane translation step.")),
                Paragraph(Text("This node records only that verified skew boundary. It does not claim additivity or real homogeneity of D, the evaluation-separated vector-valued conclusion, or all finite-order positivity. Those require the unresolved cross-plane translation bridge from the original C128 source."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var e = V("E");
        var s = V("S");
        var d = V("D");
        var alpha = V("alpha");
        var x = V("x");
        var y = V("y");
        var symmetric = All("x", e, All("y", e,
            Equal(Call("S", x, y), Call("S", y, x))));
        var psd = Call("ThreeLabelPSD", s, d, alpha);
        var conclusion = All("x", e, All("y", e,
            Equal(Call("alpha", Call("D", y, x)),
                Seq(Minus, Call("alpha", Call("D", x, y))))));
        var body = Seq(Paren(symmetric), Sp, Land, Sp, Paren(psd),
            Sp, Rightarrow, Sp, conclusion);
        return All("E", Call("Type"),
            Seq(OpenBracket, Call("AddCommGroup", e), CloseBracket, Sp,
                OpenBracket, Call("Module", Real, e), CloseBracket, Comma, Sp,
                All("S", Call("LinearMap", Real, e, Call("LinearMap", Real, e, e)),
                    All("D", Call("Function", e, Call("Function", e, e)),
                        All("alpha", Call("LinearMap", Real, e, Real), body)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
}
