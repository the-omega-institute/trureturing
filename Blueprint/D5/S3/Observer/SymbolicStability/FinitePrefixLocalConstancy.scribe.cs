using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.SymbolicStability;

internal sealed class FinitePrefixLocalConstancyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite symbolic prefix is locally constant off its boundary union.",
        H("Finite Prefix Local Constancy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-symbolic-prefix-is-locally-constant-off-boundaries"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/SymbolicStability/FinitePrefixLocalConstancy."
                    + "finite_prefix_locally_constant_off_boundary"),
                H("A finite prefix has one common stability radius"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the nth symbol map be locally constant away from its nth boundary. "
                            + "If a point avoids the union of the first N boundaries, then one "
                            + "positive metric radius makes all N symbols constant at once.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no complete theorem matching this common-radius "
                            + "statement. The Lean proof applies Filter.eventually_all to combine "
                            + "the finite family of neighborhood properties, then applies "
                            + "Metric.eventually_nhds_iff to extract the positive radius. The "
                            + "related LocallyConstant.unflip construction assumes global local "
                            + "constancy and is therefore stronger than the pointwise input here."))),
                DescribeRole.Theorem))));

    private static Formula StabilityFormula()
    {
        Formula n = F.Id("n");
        Formula nBound = Seq(n, Sp, Lt, Sp, F.Id("N"));
        Formula thetaPrime = Seq(Theta, Apos);
        Formula symbolAtPrime = Seq(
            F.Id("w"), Underscore, Grp(n), Open, thetaPrime, Close);
        Formula symbolAtPoint = Seq(
            F.Id("w"), Underscore, Grp(n), Open, Theta, Close);
        return Disp(Seq(
            Operatorname, Grp(F.Id("LocallyConstantOff")), Open, F.Id("w"), Comma, Sp,
            F.Id("B"), Close, Sp, Land, Sp,
            Theta, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("outsidePrefixBoundary")), Open, F.Id("B"), Comma, Sp,
            F.Id("N"), Close, Sp, Rightarrow, Sp,
            Exists, Sp, Varepsilon, Sp, Gt, Sp, D(0), Comma, Esc,
            Forall, Sp, thetaPrime, Comma, Esc,
            F.Id("d"), Open, thetaPrime, Comma, Sp, Theta, Close, Sp, Lt, Sp, Varepsilon,
            Sp, Rightarrow, Sp, Forall, Sp, n, Comma, Sp, nBound, Comma, Esc,
            symbolAtPrime, Sp, Eq, Sp, symbolAtPoint, Dot));
    }
}
