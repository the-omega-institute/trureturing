using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class GoldenDesubstitutionZeckendorfDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify golden substitution boundaries and terminal desubstitution indices through "
            + "uniform shifts of canonical Zeckendorf digits.",
        H("Golden Desubstitution in Zeckendorf Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-displacement-decode"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_eq_displacement_decode"),
                H("Golden substitution starts are displacement decodes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("goldenSubstStart")), Open, F.Id("n"), Close,
                    Eq, Operatorname, Grp(F.Id("displacementDecode")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The block-start count and the Zeckendorf displacement decode have the same "
                        + "shifted golden Beatty floor formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-wdigits"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_subst_start_wdigits"),
                H("A block start shifts every Zeckendorf digit once"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("wdigits")), Open,
                    Operatorname, Grp(F.Id("goldenSubstStart")), Open, F.Id("n"), Close, Close,
                    Eq, Operatorname, Grp(F.Id("map")), Open, F.Id("k"), Sp, Mapsto, Sp,
                    F.Id("k"), Plus, D(1), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("n"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Uniformly adding one preserves the nonadjacent Zeckendorf conditions, and "
                        + "uniqueness identifies the shifted list as the block start digits."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-path-wdigits"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_path_iff"),
                H("Desubstitution paths are uniform digit shifts"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, F.Id("m"), InMacro, Sp, Mathbb,
                    Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("ReflTransGen")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close,
                    Open, F.Id("n"), Comma, F.Id("m"), Close, Sp, Iff, Sp,
                    Exists, Sp, F.Id("r"), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("n"), Close,
                    Eq, Operatorname, Grp(F.Id("map")), Open, F.Id("k"), Sp, Mapsto, Sp,
                    F.Id("k"), Plus, F.Id("r"), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("m"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction over the reflexive-transitive closure accumulates one digit shift "
                        + "per step; conversely, an explicit block-start iterate realizes every "
                        + "uniform shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-terminal-wdigits"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionZeckendorf.golden_desubstitution_terminal_iff"),
                H("Terminal desubstitution is arithmetic in Zeckendorf digits"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, F.Id("m"), InMacro, Sp, Mathbb,
                    Grp(F.Id("N")), Comma, Esc, Left, Open,
                    Operatorname, Grp(F.Id("ReflTransGen")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close,
                    Open, F.Id("n"), Comma, F.Id("m"), Close, Sp, Land, Sp,
                    Left, Open, F.Id("m"), Eq, D(0), Sp, Lor, Sp,
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("m"), Close,
                    Eq, F.Id("false"), Right, Close, Right, Close, Sp, Iff, Sp,
                    Left, Open, Left, Open, F.Id("n"), Eq, D(0), Sp, Land, Sp,
                    F.Id("m"), Eq, D(0), Right, Close, Sp, Lor, Sp,
                    Exists, Sp, F.Id("r"), Comma, Sp, Left, Open, D(2), InMacro, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("m"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("n"), Close,
                    Eq, Operatorname, Grp(F.Id("map")), Open, F.Id("k"), Sp, Mapsto, Sp,
                    F.Id("k"), Plus, F.Id("r"), Comma, Sp,
                    Operatorname, Grp(F.Id("wdigits")), Open, F.Id("m"), Close, Close,
                    Right, Close, Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero path is isolated because zero has no occupied digits. Every other "
                        + "terminal has least digit two, exactly the false-letter criterion, while "
                        + "its ancestors are the uniform upward shifts of that digit list."))),
                DescribeRole.Theorem))));
}
