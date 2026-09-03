using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class GlobalBitCumulantObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single radial tensor-power parameter cannot encode every shift-dependent cumulant.",
        H("A Global-Bit Obstruction for Shift-Dependent Cumulants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-global-bit-cannot-encode-all-pair-cumulants"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GlobalBitCumulantObstruction."
                        + "one_global_bit_cannot_encode_all_pair_cumulants"),
                H("One radial tensor square misses an explicit shift pattern"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A one-bit radial model produces pair cumulants of the form scale times "
                            + "delta_i delta_j. Such a rank-one family has a load-bearing nonzero "
                            + "closure law: nonzero correlations on pairs 01 and 12 force the "
                            + "correlation on pair 02 to be nonzero.")),
                    Paragraph(Text(
                        "The explicit symmetric three-shift target instead has adjacent values "
                            + "K_01=K_12=1 and distance-two value K_02=0. It therefore has no "
                            + "representation by one displacement vector and one global scale.")),
                    Paragraph(Text(
                        "A separate public control theorem represents the constant-one pair "
                            + "family, showing that the obstruction is caused by shift structure "
                            + "rather than an empty radial model class."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula radial01 = Sub(F.Id("R"), D(0, 1));
        Formula radial12 = Sub(F.Id("R"), D(1, 2));
        Formula radial02 = Sub(F.Id("R"), D(0, 2));
        Formula target01 = Sub(F.Id("K"), D(0, 1));
        Formula target12 = Sub(F.Id("K"), D(1, 2));
        Formula target02 = Sub(F.Id("K"), D(0, 2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Sub(F.Id("R"), F.Id("ij")), Open, F.Id("c"), Comma, Sp, DeltaLower, Close,
            Sp, Eq, Sp, F.Id("c"), Sp,
            DeltaLower, Underscore, Grp(F.Id("i")), Sp,
            DeltaLower, Underscore, Grp(F.Id("j")), Comma, RowBreak, Grp(),
            target01, Sp, Eq, Sp, target12, Sp, Eq, Sp, D(1), Comma, Sp,
            target02, Sp, Eq, Sp, D(0), Comma, RowBreak, Grp(),
            Open, radial01, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            radial12, Sp, Neq, Sp, D(0), Close, Sp, Rightarrow, Sp,
            radial02, Sp, Neq, Sp, D(0), Comma, RowBreak, Grp(),
            Neg, Sp, Exists, Sp, F.Id("c"), Comma, Sp, DeltaLower, Comma, Sp,
            F.Id("R"), Open, F.Id("c"), Comma, Sp, DeltaLower, Close,
            Sp, Eq, Sp, F.Id("K"), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
