using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class GoldenDesubstitutionNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Organize golden desubstitution as a terminating deterministic rewrite system and "
            + "identify its unique terminal indices.",
        H("Golden Desubstitution Normal Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-step"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep"),
                H("One golden desubstitution step"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("x"), Comma, Sp,
                    F.Id("y"), Close, Iff, F.Id("x"), Neq, D(0), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("goldenSubstStart")), Open, F.Id("y"), Close,
                    Eq, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero substitution-block boundary rewrites to the unique source "
                        + "index whose block begins there."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-strict-descent"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_lt"),
                H("Each desubstitution step strictly decreases the index"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, F.Id("y"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("x"), Comma,
                    F.Id("y"), Close, Sp, Rightarrow, Sp, F.Id("y"), Lt, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive source prefix contains the initial true letter, so its "
                        + "substitution boundary lies strictly beyond the source index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-termination"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_termination"),
                H("Golden desubstitution terminates"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("WellFounded")), Open,
                    Operatorname, Grp(F.Id("swap")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural index is a well-founded measure because every reverse-edge "
                        + "predecessor is strictly smaller."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-determinism"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_deterministic"),
                H("Golden desubstitution is deterministic"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, F.Id("y"), Comma, F.Id("z"),
                    InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("x"), Comma,
                    F.Id("y"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("x"), Comma,
                    F.Id("z"), Close, Sp, Rightarrow, Sp, F.Id("y"), Eq, F.Id("z")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strict monotonicity makes the block-start map injective, so one boundary "
                        + "cannot have two source indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-local-confluence"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_localConfluence"),
                H("Golden desubstitution is locally confluent"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("h"), Comma, F.Id("a"), Comma, F.Id("b"), Comma, Esc,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("h"), Comma,
                    F.Id("a"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("h"), Comma,
                    F.Id("b"), Close, Sp, Rightarrow, Sp, Exists, Sp, F.Id("c"), Comma, Sp,
                    Operatorname, Grp(F.Id("ReflTransGen")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close,
                    Open, F.Id("a"), Comma, F.Id("c"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("ReflTransGen")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close,
                    Open, F.Id("b"), Comma, F.Id("c"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Deterministic one-step reducts are equal, so both branches join "
                        + "reflexively at that common reduct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-desubstitution-terminal-characterization"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.desubStep_irreducible_iff"),
                H("Terminal indices are zero or false golden-word positions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Exists, Sp, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("desubStep")), Open, F.Id("m"), Comma,
                    F.Id("x"), Close, Sp, Iff, Sp, F.Id("m"), Eq, D(0), Sp, Lor, Sp,
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("m"), Close,
                    Eq, F.Id("false")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Recognizability identifies every true position with a substitution-block "
                        + "boundary. The nonzero guard leaves zero irreducible and prevents the "
                        + "boundary at zero from becoming a self-loop."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unique-golden-desubstitution-terminal"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Powers/GoldenDesubstitutionNormalForm.golden_desubstitution_unique_terminal"),
                H("Every index has a unique golden desubstitution terminal"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Exists, Bang, Sp, F.Id("m"), Comma, Sp,
                    Operatorname, Grp(F.Id("ReflTransGen")), Open,
                    Operatorname, Grp(F.Id("desubStep")), Close,
                    Open, F.Id("n"), Comma, F.Id("m"), Close, Sp, Land, Sp,
                    Left, Open, F.Id("m"), Eq, D(0), Sp, Lor, Sp,
                    Operatorname, Grp(F.Id("goldenWord")), Open, F.Id("m"), Close,
                    Eq, F.Id("false"), Right, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen abstract Newman theorem applies to strict descent and the "
                        + "deterministic local-confluence join. Replacing irreducibility by its "
                        + "golden-word characterization gives the stated unique terminal."))),
                DescribeRole.Theorem))));
}
