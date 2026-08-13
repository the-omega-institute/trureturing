using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class GoldenDesubstitutionDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measure golden desubstitution paths exactly and decode the resulting terminal digits.",
        H("Golden Desubstitution Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-exact-length"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_exact_length_iff"),
                H("Exact desubstitution path length"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, F.Id("m"), Sp, F.Id("r"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Left, Open, Exists, Sp, F.Id("xs"), Comma, Sp,
                    F.Id("length"), Open, F.Id("xs"), Close, Eq, F.Id("r"), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("IsChain")), Open, Operatorname,
                    Grp(F.Id("desubStep")), Sp, F.Id("n"), Comma, Sp, F.Id("xs"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("getLast")), Open,
                    F.Id("n"), Comma, Sp, F.Id("xs"), Close, Eq, F.Id("m"), Right, Close,
                    Sp, Iff, Sp, Left, Open, F.Id("m"), Neq, D(0), Sp, Lor, Sp,
                    F.Id("r"), Eq, D(0), Right, Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("n"), Close, Eq,
                    Operatorname, Grp(F.Id("map")), Open, F.Id("k"), Sp, Mapsto, Sp,
                    F.Id("k"), Plus, F.Id("r"), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("m"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero endpoint admits exactly the number of steps recorded by the "
                        + "uniform Zeckendorf shift; zero is permitted only at depth zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-nf-wdigits-decode"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionDepth.golden_desubstitution_nf_eq_wdigits_decode"),
                H("Normal form is the closed shifted-digit decode"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("nf")), Open, Operatorname, Grp(F.Id("desubStep")),
                    Comma, Sp, Operatorname, Grp(F.Id("desubStepTermination")), Comma, Sp,
                    Operatorname, Grp(F.Id("desubStepLocalConfluence")), Comma, Sp, F.Id("n"), Close,
                    Eq, Operatorname, Grp(F.Id("decode")), Open,
                    Operatorname, Grp(F.Id("map")), Open, F.Id("k"), Sp, Mapsto, Sp,
                    F.Id("k"), Minus, F.Id("shift"), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("n"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unique terminal is obtained by shifting every occupied Fibonacci index "
                        + "down until the least digit reaches its floor, with zero handled separately."))),
                DescribeRole.Theorem))));
}
