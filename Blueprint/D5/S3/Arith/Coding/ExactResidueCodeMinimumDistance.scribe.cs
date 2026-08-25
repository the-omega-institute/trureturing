using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ExactResidueCodeMinimumDistanceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/ExactResidueCodeMinimumDistance."
            + "exact_residue_code_minimum_distance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum Hamming distance of a bounded residue code is determined exactly "
            + "by the largest product-bounded coordinate subset.",
        H("Exact Residue-Code Minimum Distance"),
        Blocks(Describe.Lean(
            DescribeId.Create("exact-residue-code-minimum-distance"),
            DeclarationHandle.Create(Declaration),
            H("Exact residue-code minimum distance"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The minimum-distance object is the infimum of the Hamming distances "
                        + "between distinct messages in the bounded range. The blind-coordinate "
                        + "object is independently the maximum cardinality of a coordinate "
                        + "subset whose modulus product is below that range.")),
                Paragraph(Text(
                    "Sorting makes the first r moduli the least product among all r-coordinate "
                        + "subsets. The maximal blind count therefore lies between two adjacent "
                        + "prefix thresholds, and the frozen dynamic-range characterization "
                        + "turns those thresholds into the exact distance equality."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula moduli = F.Id("m");
        Formula length = F.Id("n");
        Formula range = F.Id("K");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula modulusI = NamedCall(F.Id("m"), i);
        Formula modulusJ = NamedCall(F.Id("m"), j);
        Formula minimum = NamedCall(
            F.Id("residueMinimumDistance"), moduli, length, range);
        Formula blindCount = NamedCall(
            F.Id("maximumBlindCoordinateCount"), moduli, length, range);
        Formula fullProduct = Seq(
            Prod, Underscore, Grp(Seq(i, Sp, Lt, Sp, length)), Sp, modulusI);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, moduli, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma,
            Sp, length, Comma, Sp, range, Sp, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            Open,
            Open, Forall, Sp, i, Comma, Sp,
            i, Sp, Lt, Sp, length, Sp, Rightarrow, Sp,
            D(2), Sp, Leq, Sp, modulusI, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, length,
            Sp, Rightarrow, Sp, modulusI, Sp, Lt, Sp, modulusJ, Close,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, length, Sp, Land, Sp,
            j, Sp, Lt, Sp, length, Sp, Land, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Gcd, Open, modulusI, Comma, Sp, modulusJ, Close, Sp, Eq, Sp, D(1), Close,
            Sp, Land, RowBreak, Grp(),
            D(2), Sp, Leq, Sp, range, Sp, Leq, Sp, fullProduct,
            Close, Sp, Rightarrow, RowBreak, Grp(),
            minimum, Sp, Eq, Sp, length, Sp, Minus, Sp, blindCount, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula NamedCall(Formula name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}
