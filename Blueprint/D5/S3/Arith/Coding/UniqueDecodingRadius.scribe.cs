using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class UniqueDecodingRadiusDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/UniqueDecodingRadius.unique_decoding_radius";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A minimum-distance code has a unique nearby codeword below half the minimum "
            + "distance, including the canonical integral correction radius.",
        H("Unique Decoding Radius"),
        Blocks(Describe.Lean(
            DescribeId.Create("minimum-distance-gives-the-unique-decoding-radius"),
            DeclarationHandle.Create(Declaration),
            H("Minimum distance gives the unique decoding radius"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "If the received word and a competing codeword are each within e "
                        + "coordinates of the true word, the Hamming triangle inequality "
                        + "puts the two codewords at distance at most 2e. The strict "
                        + "minimum-distance bound therefore forces them to coincide.")),
                Paragraph(Text(
                    "Natural-number division makes twice floor((d - 1) / 2) strictly less "
                        + "than every positive d. At d = 0, radius zero still has a unique "
                        + "candidate because zero Hamming distance is equality."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula code = F.Id("C");
        Formula distance = F.Id("d");
        Formula sent = F.Id("c");
        Formula received = F.Id("r");
        Formula radius = F.Id("e");
        Formula guaranteedRadius = new Formula.Floor(new Formula.Fraction(
            Seq(distance, Sp, Minus, Sp, D(1)),
            D(2)));

        Formula arbitraryClause = Seq(
            Forall, Sp, sent, Comma, Sp, received, Comma, Sp, radius, Comma, Sp,
            Open,
            sent, Sp, InMacro, Sp, code, Sp, Land, Sp,
            HammingDistance(received, sent), Sp, Leq, Sp, radius, Sp, Land, Sp,
            D(2), Sp, Times, Sp, radius, Sp, Lt, Sp, distance,
            Close, Sp, Rightarrow, Sp,
            UniqueCandidate(code, received, radius));
        Formula guaranteedClause = Seq(
            Forall, Sp, sent, Comma, Sp, received, Comma, Sp,
            Open,
            sent, Sp, InMacro, Sp, code, Sp, Land, Sp,
            HammingDistance(received, sent), Sp, Leq, Sp, guaranteedRadius,
            Close, Sp, Rightarrow, Sp,
            UniqueCandidate(code, received, guaranteedRadius));

        return Disp(Seq(
            MinimumDistance(code, distance), Sp, Rightarrow,
            RowBreak, Grp(),
            Open, arbitraryClause, Close, Sp, Land,
            RowBreak, Grp(),
            Open, guaranteedClause, Close, Dot));
    }

    private static Formula UniqueCandidate(
        Formula code,
        Formula received,
        Formula radius)
    {
        Formula candidate = F.Id("x");
        Formula competitor = F.Id("y");
        Formula competitorProperty = Seq(
            competitor, Sp, InMacro, Sp, code, Sp, Land, Sp,
            HammingDistance(received, competitor), Sp, Leq, Sp, radius);

        return Seq(
            Exists, Sp, candidate, Comma, Sp,
            candidate, Sp, InMacro, Sp, code, Sp, Land, Sp,
            HammingDistance(received, candidate), Sp, Leq, Sp, radius, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, competitor, Comma, Sp,
            Open, competitorProperty, Close, Sp, Rightarrow, Sp,
            competitor, Sp, Eq, Sp, candidate, Close);
    }

    private static Formula MinimumDistance(Formula code, Formula distance) =>
        Call("MinDistanceAtLeast", code, distance);

    private static Formula HammingDistance(Formula first, Formula second) =>
        Call("hammingDist", first, second);
}
