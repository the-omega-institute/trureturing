using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class SuHuTable41Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/SuHuTable41.";
    private static readonly LibraryNoteRef SuHu = LibraryNoteRef.Create("D5/L/Estimation/suhu2026fullnegative");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact negative dependence calculations for the Su and Hu four-coordinate law.",
        H("Su and Hu Table 4.1"),
        Blocks(
            Describe.Lean(DescribeId.Create("su-hu-table-41-law"),
                DeclarationHandle.Create(Prefix + "tablePMF"), H("The published probability law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(SuHu),
                Blocks(Paragraph(Text("Both pairs of ternary coordinates use lexicographic order. The displayed integer "
                    + "weights sum to 99,999, and each weight is divided by that total."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("su-hu-table-41-positive-covariance"),
                DeclarationHandle.Create(Prefix + "table_positive_covariance"), H("Exact positive covariance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, Apply("tablePMF", F.Id("x")), Sp, Gt, Sp, D(0), Close,
                    Sp, Land, Sp, Exists, Sp, F.Id("I"), Comma, Sp, F.Id("J"), Comma, Sp,
                    F.Id("f"), Comma, Sp, F.Id("g"), Comma, Sp,
                    Apply("Disjoint", F.Id("I"), F.Id("J")), Sp, Land, Sp,
                    Apply("Monotone", F.Id("f")), Sp, Land, Sp, Apply("Monotone", F.Id("g")), Sp, Land, Sp,
                    Apply("cov", F.Id("tablePMF"), Seq(F.Id("f"), Sp, Circ, Sp, Apply("project", F.Id("I"))),
                        Seq(F.Id("g"), Sp, Circ, Sp, Apply("project", F.Id("J")))), Sp, Eq, Sp,
                    new Formula.Fraction(D(1, 1, 4, 1, 0, 6, 7), D(9, 9, 9, 9, 8, 0, 0, 0, 0, 1)),
                    Sp, Gt, Sp, D(0)))), AssessedProvenance.FromLiterature(SuHu),
                Blocks(Paragraph(Text("Every table entry has positive mass. The two increasing tests indicate that "
                    + "both coordinates in the corresponding pair are at least one. Each event has weight 39,649, "
                    + "and their intersection has weight 15,732. Their covariance is 1,141,067 divided by 9,999,800,001."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su-hu-table-41-attainment"),
                DeclarationHandle.Create(Prefix + "table_attainment"), H("Attainment at 81"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, Apply("tablePMF", F.Id("x")), Sp, Gt, Sp, D(0), Close,
                    Sp, Land, Sp, Apply("marginalProduct", F.Id("tablePMF")), Sp, Eq, Sp, D(8, 1),
                    Sp, Land, Sp, Apply("FullNRD", F.Id("tablePMF")), Sp, Land, Sp, Neg,
                    Apply("NA", F.Id("tablePMF"))))), AssessedProvenance.FromRepo(SuHu),
                Blocks(Paragraph(Text("For each conditioning block, enumerate comparable tuples and upper sets on "
                    + "the complementary block. Each upper set on a disjoint response block pulls back to one "
                    + "of these upper sets. Compare integer fiber weights by cross multiplication and lift the "
                    + "upper-event inequalities to increasing real tests. Strict positivity gives four marginal "
                    + "supports of size three. The exact positive covariance violates negative association."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("su-hu-table-41-refuted-implication"),
                DeclarationHandle.Create(Prefix + "claim"), H("The implication on four ternary coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(SuHu),
                Blocks(Paragraph(Text("Every strictly positive probability mass function on the four-coordinate ternary "
                    + "product with full negative regression would have negative association."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("su-hu-table-41-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("The implication fails"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromLiterature(SuHu),
                Blocks(Paragraph(Text("The strictly positive Table 4.1 law satisfies full negative regression, and the "
                    + "positive covariance on its disjoint upper events contradicts negative association."))),
                DescribeRole.Theorem))));
    private static Formula Apply(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
