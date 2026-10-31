using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class TreeMarkovStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite normalized tree replacement schedules telescope in total variation with the degree-weighted node charge and the sharp edge coefficient.",
        H("Tree Markov Replacement Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("degree-weighted-tree-replacement-bound"),
                DeclarationHandle.Create("D5/S3/TotalVariation/TreeMarkovStability.tree_markov_total_variation_bound"),
                H("Degree-weighted tree replacement bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Operatorname, Grp(F.Id("TV")), Open, F.Id("P"), Comma, Sp, F.Id("Q"), Close,
                    Le, Sp, Sum, Sp, Underscore, Grp(F.Id("e")), Sp, F.Id("edge"), Open, F.Id("e"), Close,
                    Plus, Sp, Sum, Sp, Underscore, Grp(F.Id("v")), Sp,
                    Open, F.Id("degree"), Open, F.Id("v"), Close, Minus, D(1), Close,
                    Cdot, Sp, F.Id("node"), Open, F.Id("v"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite hybrid path is telescoped by the total-variation triangle inequality. " +
                    "The charge identity records one node contribution for every non-root child replacement."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("sharp-edge-coefficient-one"),
                DeclarationHandle.Create("D5/S3/TotalVariation/TreeMarkovStability.edge_coefficient_one_sharp"),
                H("Sharp edge coefficient one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("c"), Lt, D(1), Sp, Rightarrow, Sp,
                    F.Id("TV"), Open, F.Id("P"), Comma, Sp, F.Id("Q"), Close,
                    Gt, Sp, F.Id("c"), Cdot, F.Id("TV"), Open, F.Id("P"), Comma, Sp, F.Id("Q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal and anti-diagonal Bool edge laws both have unit total variation, " +
                    "so a coefficient below one cannot bound the joint edge discrepancy."))),
                DescribeRole.Theorem
            ))));
}
