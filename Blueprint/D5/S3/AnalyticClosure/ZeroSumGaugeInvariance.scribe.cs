using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class ZeroSumGaugeInvarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero-sum local gauge shift leaves the global completion sum unchanged.",
        H("Zero-Sum Gauge Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-sum-gauge-invariance"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/ZeroSumGaugeInvariance.zero_sum_gauge_invariance"),
                H("Zero-sum shifts preserve the global sum"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The local ledger is represented by an absolutely summable real "
                            + "family localContribution, and shift is another absolutely "
                            + "summable family. When the shift sums to zero, replacing each "
                            + "local term by localContribution plus shift preserves the "
                            + "global sum."))),
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

    private static Formula Tsum(Formula binder, Formula body) =>
        Seq(SigmaLower, Underscore, Grp(binder), Sp, body);

    private static Formula TheoremFormula()
    {
        Formula v = F.Id("V");
        Formula local = F.Id("localContribution");
        Formula shift = F.Id("shift");
        Formula summableLocal = Call("Summable", local);
        Formula summableShift = Call("Summable", shift);
        Formula zeroShift = Seq(Tsum(F.Id("v"), Seq(shift, Open, F.Id("v"), Close)), Sp, Eq, Sp, D(0));
        Formula changed = Tsum(
            F.Id("v"),
            Seq(Open, local, Open, F.Id("v"), Close, Sp, Plus, Sp,
                shift, Open, F.Id("v"), Close, Close));
        Formula original = Tsum(F.Id("v"), Seq(local, Open, F.Id("v"), Close));
        return Disp(Seq(
            Forall, Sp, v, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            local, Comma, Sp, shift, Colon, Sp, v, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            summableLocal, Sp, Land, Sp, summableShift, Sp, Land, Sp, zeroShift,
            Sp, Rightarrow, Sp, changed, Sp, Eq, Sp, original, Dot));
    }
}
