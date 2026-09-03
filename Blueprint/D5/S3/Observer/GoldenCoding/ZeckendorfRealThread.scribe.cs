using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class ZeckendorfRealThreadDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenCoding/ZeckendorfRealThread."
            + "zeckendorf_real_thread_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete Zeckendorf thread reconstructs a nonnegative real number.",
        H("Zeckendorf Real Thread Reconstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("zeckendorf-real-thread-injective"),
            DeclarationHandle.Create(Declaration),
            H("The complete Zeckendorf thread is injective"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "At level N, the source quantization is the natural floor of phi to "
                        + "the N times x. Its thread coordinate is the repository's "
                        + "canonical W encoding of that natural number.")),
                Paragraph(Text(
                    "Equal threads have equal quantizations because the W encoding is an "
                        + "equivalence. Distinct nonnegative reals have a positive gap, "
                        + "and some golden power expands that gap beyond the width of a "
                        + "single natural-floor interval."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula nonnegativeReal = new Formula.Subscript(
            Seq(Mathbb, Grp(F.Id("R"))), Seq(Geq, Sp, D(0)));
        Formula level = F.Id("N");
        Formula x = F.Id("x");
        Formula quantization = F.Id("q");
        Formula thread = F.Id("Z");
        Formula quantizationAt = Call("q", level, x);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            F.Id("let"), Sp, quantization, Colon, Sp, natural, Sp, To, Sp,
            nonnegativeReal, Sp, To, Sp, natural, Sp, Colon, Eq, Sp,
            Open, level, Mapsto, Sp, Open, x, Mapsto, Sp,
            Lfloor, Varphi, Caret, Grp(level), Sp, Cdot, Sp, x, Rfloor,
            Close, Close, Semi, RowBreak, Grp(),
            F.Id("let"), Sp, thread, Colon, Sp,
            nonnegativeReal, Sp, To, Sp, natural, Sp, To, Sp,
            Operatorname, Grp(F.Id("WDigitString")), Sp, Colon, Eq, Sp,
            Open, x, Mapsto, Sp, Open, level, Mapsto, Sp,
            Call("wEncoding", quantizationAt), Close, Close,
            Semi, RowBreak, Grp(),
            Call("Injective", thread), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
