using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class LocalPrecisionUnitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime's p-adic norm fixes its real logarithmic precision unit.",
        H("Local Precision Unit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-precision-unit"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/LocalPrecisionUnit.local_precision_unit"),
                H("The logarithmic unit is unique"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p, precisionLength is the source logarithmic length "
                            + "constructed from the canonical p-adic norm. Its exponential "
                            + "weight equals the norm of p, the value is log p, and no other "
                            + "real length has that weight.")),
                    Paragraph(Text(
                        "The final clause rewrites the real power p^(-s) as the exponential "
                            + "of -s log p for every real s."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula NormP(Formula p) =>
        Seq(Vert, Sp, p, Sp, Vert, Underscore, F.Id("p"));

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula length = Call("precisionLength", p);
        Formula norm = NormP(p);
        Formula expWeight = Seq(Exp, Open, Minus, length, Close);
        Formula realLog = Seq(Log, Open, p, Close);
        Formula uniqueness = Seq(
            Forall, Sp, F.Id("ell"), Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Exp, Open, Minus, F.Id("ell"), Close, Sp, Eq, Sp, norm, Sp, Rightarrow, Sp,
            F.Id("ell"), Sp, Eq, Sp, length);
        Formula powerIdentity = Seq(
            Forall, Sp, F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            p, Caret, Grp(Seq(Minus, F.Id("s"))), Sp, Eq, Sp,
            Exp, Open, Seq(Minus, F.Id("s"), Sp, Times, Sp, realLog), Close);
        return Disp(Seq(
            Forall, Sp, p, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("Fact", Seq(p, Dot, F.Id("Prime"))), Sp, Rightarrow, Sp,
            Open, expWeight, Sp, Eq, Sp, norm, Sp, Land, Sp,
            length, Sp, Eq, Sp, realLog, Sp, Land, Sp, uniqueness, Close,
            Sp, Land, Sp, powerIdentity, Dot));
    }
}
