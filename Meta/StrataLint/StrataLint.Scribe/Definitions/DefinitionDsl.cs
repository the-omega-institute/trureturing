using StrataLint.Engine;

namespace StrataLint.Scribe.Definitions;

internal static class DefinitionDsl
{
    internal static DocumentHeader Header(string gid, string digest) =>
        DocumentHeader.Create(
            GidRef.Create(gid),
            Generality.Instance,
            GidRef.Create("D5/B/" + gid["D5/".Length..]),
            new EvidenceMirror.Waiver(WaiverReason.Create("algebraically-proved")),
            [AnchorRef.Create("GICT-v3.6-I.1-definition-1.4")],
            Digest.Create(digest));

    internal static Heading H(string value) => Heading.Create(value);

    internal static TextRun T(string value) => TextRun.Create(value);

    internal static Inline Text(string value) => new Inline.Text(T(value));

    internal static Inline Math(Formula value) => new Inline.InlineFormula(value);

    internal static Inline Ref(string value) => new Inline.GidReference(GidRef.Create(value));

    internal static DocumentBlock Paragraph(params Inline[] content) =>
        new DocumentBlock.Paragraph(InlineSequence.Create(content));

    internal static BlockSequence Blocks(params DocumentBlock[] content) =>
        BlockSequence.Create(content);

    internal static Formula Id(string value) =>
        new Formula.Symbol(FormulaIdentifier.Create(value));

    internal static Formula Num(long value) => new Formula.Number(value);

    internal static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    internal static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    internal static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    internal static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    internal static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    internal static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
}
