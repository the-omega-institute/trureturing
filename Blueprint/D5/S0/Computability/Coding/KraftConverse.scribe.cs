using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class KraftConverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every bounded multiset satisfying the finite Kraft bound is realized by a prefix-free binary code.",
        H("Finite Binary Kraft Converse"),
        Blocks(
            Paragraph(Text(
                "For lengths bounded by a common depth N, multiplying the usual Kraft sum "
                + "by 2^N gives an exact natural-number inequality. This avoids any appeal "
                + "to real-number rounding while retaining repeated prescribed lengths.")),
            Describe.Lean(
                DescribeId.Create("finite-binary-kraft-converse"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/KraftConverse.exists_isPrefixFree_code_of_kraft"),
                H("The integer-scaled Kraft bound constructs a prefix-free code"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("lengths"), Comma, Sp, F.Id("N"), Comma, Sp,
                    Open, Forall, Sp, F.Id("l"), Sp, InMacro, Sp, F.Id("lengths"), Comma,
                    Sp, F.Id("l"), Sp, Leq, Sp, F.Id("N"), Close, Sp, Land, Sp,
                    Open, Sum, Underscore,
                    Grp(F.Id("l"), Sp, InMacro, Sp, F.Id("lengths")), Sp,
                    new Formula.Power(D(2), Grp(F.Id("N"), Sp, Minus, Sp, F.Id("l"))),
                    Sp, Leq, Sp, new Formula.Power(D(2), F.Id("N")), Close,
                    Sp, Rightarrow, Sp, Exists, Sp, F.Id("code"), Comma, Sp,
                    Operatorname, Grp(F.Id("Nodup")), Open, F.Id("code"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("lengthMultiset")),
                    Open, F.Id("code"), Close, Sp, Eq, Sp, F.Id("lengths"),
                    Sp, Land, Sp, Operatorname, Grp(F.Id("IsPrefixFree")),
                    Open, F.Id("code"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sort the prescribed lengths and add codewords from shortest to "
                        + "longest. At each depth, a union bound counts the binary vectors "
                        + "already occupied by earlier prefix cylinders. The scaled Kraft "
                        + "budget leaves a vector outside that union, so adjoining it preserves "
                        + "prefix freedom and list nodupness.")),
                    Paragraph(Text(
                        "The hypothesis sum 2^(N-l) <= 2^N is exactly equivalent, for these "
                        + "bounded lengths, to sum 2^(-l) <= 1. The resulting code has exactly "
                        + "the input length multiset, including multiplicities."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/PrefixFreeCode")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/KraftInequality"))]));
}
