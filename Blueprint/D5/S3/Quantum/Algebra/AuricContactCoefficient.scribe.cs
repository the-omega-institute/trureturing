using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class AuricContactCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/AuricContactCoefficient.";

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(V(name)), Open,
            Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray()), Close);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(D(2)));
    private static Formula Hypotheses() => Seq(
        Ne(V("x"), D(0)), Sp, Land, Sp, D(1), Lt, Sq(V("y")));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Auric scalar contact coefficients admit explicit factorizations at the cost centre, with nonvanishing central coefficients.",
        H("Auric contact coefficient identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("auric-contact-coefficient-identities"),
                DeclarationHandle.Create(Prefix + "lemma_46_3"),
                H("Explicit coefficient identities at t = 1/4"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, V("x"), Comma, Sp, V("y"), Comma, Sp, V("t"), Sp,
                    InMacro, Sp, Mathbb, Grp(V("R")), Comma, Esc,
                    Hypotheses(), Sp, Rightarrow, Sp,
                    Open,
                    Call("fOne", V("x"), V("y")), Eq, Call("fOneFactored", V("x"), V("y")), Sp, Land, Sp,
                    Call("gZero", V("x"), V("y")), Eq, Call("gZeroFactored", V("x"), V("y")), Sp, Land, Sp,
                    Call("fCenter", V("x"), V("y")), Eq, Call("fCenterClosed", V("x"), V("y")), Sp, Land, Sp,
                    Call("gCenter", V("x"), V("y")), Eq, Call("gCenterClosed", V("x"), V("y")), Sp, Land, Sp,
                    Ne(Call("fCenter", V("x"), V("y")), D(0)), Sp, Land, Sp,
                    Ne(Call("gCenter", V("x"), V("y")), D(0)), Sp, Land, Sp,
                    Call("g", V("x"), V("y"), V("t")), Eq, Call("gClosed", V("x"), V("y"), V("t")),
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real coordinates satisfy x nonzero and y squared greater than one, and "
                        + "ell is the complex coordinate x + y I. The theorem expands the coefficients "
                        + "from the source-aligned scalar graph: fOne and gZero are the factored forms "
                        + "of the derivative and zero-parameter coefficients.")),
                    Paragraph(Text(
                        "At the cost centre t = 1/4, the central coefficient fCenter has real part "
                        + "(x-4)/2 and imaginary part -(5 y squared + 6 (x-1) squared)/(2y). "
                        + "The central g coefficient is (ell-2)(2 + 3 I (x+1)/(2y)); both are "
                        + "nonzero because y squared is greater than one.")),
                    Paragraph(Text(
                        "For arbitrary t, zeta is 4t and beta is 3(1+zeta), and g equals "
                        + "-(2-ell)/4 times the displayed real-affine bracket. This is the algebraic "
                        + "identity layer of Lemma 46.3 only; it does not assert the contact equations, "
                        + "the root polynomial, or the global cost lower bounds from the surrounding theory."))),
                DescribeRole.Theorem))));
}
