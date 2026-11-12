using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class TwoAnchorGramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumContext/TwoAnchorGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-anchor Gram determinants give the squared corridor area and detect independence.",
        H("Two-Anchor Gram Corridor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-anchor-gram"),
                DeclarationHandle.Create(Prefix + "twoAnchorGram"),
                H("The two-anchor Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For vectors u and v in a real inner-product space, twoAnchorGram u v "
                        + "is the 2 by 2 Gram matrix built from the vector family [u, v]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-anchor-gram-determinant-formula"),
                DeclarationHandle.Create(Prefix + "two_anchor_gram_det_formula"),
                H("The two-anchor Gram determinant formula"),
                StatementSource.FromAuthor(DeterminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant of the two-anchor Gram matrix is the squared area "
                        + "expression ‖u‖²‖v‖² − ⟪u,v⟫². This is the exact algebraic "
                        + "quantity used for the chapter's two-anchor compatibility corridor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-anchor-gram-determinant-positive"),
                DeclarationHandle.Create(Prefix + "two_anchor_gram_det_pos_iff"),
                H("Positive Gram area is equivalent to independent anchors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant is strictly positive exactly when the two vectors are "
                        + "linearly independent over ℝ. Thus the compatibility corridor has "
                        + "positive area precisely away from the collinear boundary."))),
                DescribeRole.Theorem))));

    private static Formula DeterminantFormula()
    {
        Formula E = F.Id("E");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")), Star);
        Formula norm(Formula x) => Seq(Operatorname, Grp(F.Id("norm")), Open, x, Close);
        Formula inner = Call("realInner", u, v);
        Formula rhs = Seq(norm(u), Caret, Grp(D(2)), Sp, Cdot, Sp,
            norm(v), Caret, Grp(D(2)), Sp, Minus, Sp,
            Parenthesized(Seq(inner, Caret, Grp(D(2)))));
        Formula body = Equal(Call("det", Call("twoAnchorGram", u, v)), rhs);
        Formula instances = Seq(
            OpenBracket, Call("NormedAddCommGroup", E), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", real, E), CloseBracket, Comma, Sp);
        return Disp(All("E", type, Seq(instances, All("u", E, All("v", E, body)))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
