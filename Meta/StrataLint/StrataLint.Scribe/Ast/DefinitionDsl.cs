using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class DefinitionDsl
{
    public static DocumentHeader Header(string gid, string digest, params string[] anchors) =>
        DocumentHeader.Create(
            GidRef.Create(gid),
            Generality.Instance,
            GidRef.Create("D5/B/" + gid["D5/".Length..]),
            new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
            (anchors.Length == 0 ? ["GICT-v3.6-I.1-definition-1.4"] : anchors)
                .Select(AnchorRef.Create),
            Digest.Create(digest));

    public static Heading H(string value) => Heading.Create(value);

    public static TextRun T(string value) => TextRun.Create(value);

    public static Inline Text(string value) => new Inline.Text(T(value));

    public static Inline Math(Formula value) => new Inline.InlineFormula(value);

    public static Inline Ref(string value) => new Inline.GidReference(GidRef.Create(value));

    public static DocumentBlock Paragraph(params Inline[] content) =>
        new DocumentBlock.Paragraph(InlineSequence.Create(content));

    public static BlockSequence Blocks(params DocumentBlock[] content) =>
        BlockSequence.Create(content);

    public static Formula Id(string value) =>
        new Formula.Symbol(FormulaIdentifier.Create(value));

    public static Formula Num(long value) => new Formula.Number(value);

    public static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    public static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    public static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    public static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    public static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    public static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
}
