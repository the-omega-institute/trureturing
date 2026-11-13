using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class ThreeAnchorGramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/ThreeAnchorGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-anchor Gram determinants give the squared volume expression and detect independence.",
        H("Three-Anchor Gram Corridor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-anchor-gram"),
                DeclarationHandle.Create(Prefix + "threeAnchorGram"),
                H("The three-anchor Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For vectors u, v, and w in a real inner-product space, threeAnchorGram u v w "
                        + "is the 3 by 3 Gram matrix built from the vector family [u, v, w]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-anchor-gram-determinant-formula"),
                DeclarationHandle.Create(Prefix + "three_anchor_gram_det_formula"),
                H("The three-anchor Gram determinant formula"),
                StatementSource.FromAuthor(DeterminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant of the three-anchor Gram matrix is the squared volume "
                        + "expression obtained by expanding the 3 by 3 determinant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("three-anchor-gram-determinant-positive"),
                DeclarationHandle.Create(Prefix + "three_anchor_gram_det_pos_iff"),
                H("Positive Gram volume is equivalent to independent anchors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant is strictly positive exactly when the three vectors are "
                        + "linearly independent over ℝ. Thus the three-anchor compatibility "
                        + "volume is positive precisely away from the dependent boundary."))),
                DescribeRole.Theorem))));

    private static Formula DeterminantFormula()
    {
        Formula E = F.Id("E");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")), Star);
        Formula norm(Formula x) => Seq(Operatorname, Grp(F.Id("norm")), Open, x, Close);
        Formula inner(Formula x, Formula y) => Call("realInner", x, y);
        Formula sq(Formula x) => Parenthesized(Seq(x, Caret, Grp(D(2))));
        Formula rhs = Seq(
            sq(norm(u)), Sp, Cdot, Sp, sq(norm(v)), Sp, Cdot, Sp, sq(norm(w)),
            Sp, Plus, Sp, D(2), Sp, Cdot, Sp,
            inner(u, v), Sp, Cdot, Sp, inner(u, w), Sp, Cdot, Sp, inner(v, w),
            Sp, Minus, Sp, sq(norm(u)), Sp, Cdot, Sp, sq(inner(v, w)),
            Sp, Minus, Sp, sq(norm(v)), Sp, Cdot, Sp, sq(inner(u, w)),
            Sp, Minus, Sp, sq(norm(w)), Sp, Cdot, Sp, sq(inner(u, v)));
        Formula body = Equal(Call("det", Call("threeAnchorGram", u, v, w)), rhs);
        Formula instances = Seq(
            OpenBracket, Call("NormedAddCommGroup", E), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", real, E), CloseBracket, Comma, Sp);
        return Disp(All("E", type, Seq(instances,
            All("u", E, All("v", E, All("w", E, body))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
