using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class MetallicMinimumDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S0/Asymptotics/MetallicMinimum.metallic_value_minimal_nontrivial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden ratio uniquely minimizes the positive integer members of the metallic family.",
        H("Least Nontrivial Metallic Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("least-positive-integer-metallic-value"),
            DeclarationHandle.Create(Declaration),
            H("The golden ratio is the unique least nontrivial value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The parameter-one value explicitly realizes the golden ratio. For every "
                        + "positive integer parameter, comparison of the two radicands gives the "
                        + "golden lower bound, and equality forces the parameter back to one.")),
                Paragraph(Text(
                    "The source derives positivity of the integer fusion coefficient from "
                        + "noninvertibility. The Lean statement exposes that derived condition as "
                        + "0 < n because it reuses the repository's numerical metallic family rather "
                        + "than introducing a second fusion-category carrier."))),
            DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Metallic(Formula parameter) =>
        Seq(F.Id("metallicValue"), Open, parameter, Close);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula value = Metallic(n);

        return Disp(new Formula.Aligned([
            Seq(Metallic(D(1)), Sp, Eq, Sp, Varphi, Sp, Land),
            Seq(
                Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
                D(0), Sp, Lt, Sp, n, Sp, Rightarrow),
            Seq(
                Varphi, Sp, Le, Sp, value, Sp, Land, Sp,
                Open, value, Sp, Eq, Sp, Varphi, Sp, Iff, Sp,
                n, Sp, Eq, Sp, D(1), Close, Dot),
        ]));
    }
}
