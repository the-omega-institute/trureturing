using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class GoldenDesubstitutionNfDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify the exact length of every golden desubstitution path to its chosen normal form.",
        H("Golden Desubstitution Normal-Form Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-nf-exact-depth"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNfDepth.golden_desubstitution_nf_exact_depth_iff"),
                H("Exact depth to the chosen normal form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, F.Id("r"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Left, Open, Exists, Sp, F.Id("xs"), Comma, Sp,
                    F.Id("length"), Open, F.Id("xs"), Close, Eq, F.Id("r"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("IsChain")), Open, Operatorname,
                    Grp(F.Id("desubStep")), Sp, F.Id("n"), Comma, Sp, F.Id("xs"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("getLast")), Open,
                    F.Id("n"), Comma, Sp, F.Id("xs"), Close, Eq,
                    Operatorname, Grp(F.Id("nf")), Open, Operatorname,
                    Grp(F.Id("desubStep")), Comma, Sp, Operatorname,
                    Grp(F.Id("desubStepTermination")), Comma, Sp, Operatorname,
                    Grp(F.Id("desubStepLocalConfluence")), Comma, Sp, F.Id("n"),
                    Close, Right, Close, Sp, Iff, Sp, F.Id("r"), Eq,
                    Operatorname, Grp(F.Id("desubstitutionShift")), Open,
                    F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every chain ending at the chosen normal form has the unique length measured "
                        + "by the least occupied Zeckendorf index."))),
                DescribeRole.Theorem))));
}
