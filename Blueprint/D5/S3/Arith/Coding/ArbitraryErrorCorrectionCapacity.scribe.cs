using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ArbitraryErrorCorrectionCapacityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Arith/Coding/ArbitraryErrorCorrectionCapacity."
            + "arbitrary_error_correction_capacity_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint radius-e Hamming balls force distance 2e+1 and the corresponding "
            + "mixed-modulus capacity bound.",
        H("Arbitrary Error Correction Capacity"),
        Blocks(Describe.Lean(
            DescribeId.Create("arbitrary-error-correction-forces-the-capacity-bound"),
            DeclarationHandle.Create(Declaration),
            H("Arbitrary error correction forces the capacity bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The correction premise is operational: any received word within e "
                        + "coordinates of two residue codewords forces their messages to "
                        + "coincide. Splitting the disagreement coordinates between two "
                        + "candidate words shows that their distance cannot be at most 2e.")),
                Paragraph(Text(
                    "The existing exact dynamic-range theorem then converts minimum distance "
                        + "2e+1 into the product of the first n-2e moduli. The result does not "
                        + "need the ambient upper bound K at most the full modulus product."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula range = F.Id("K");
        Formula radius = F.Id("e");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula received = F.Id("r");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula requiredDistance = Seq(D(2), Sp, Times, Sp, radius, Sp, Plus, Sp, D(1));
        Formula prefixLength = Seq(n, Sp, Minus, Sp, D(2), Sp, Times, Sp, radius);

        Formula ordered = Seq(
            Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, n,
            Sp, Rightarrow, Sp, Call("m", i), Sp, Lt, Sp, Call("m", j));
        Formula positive = Seq(
            Forall, Sp, i, Comma, Sp, i, Sp, Lt, Sp, n,
            Sp, Rightarrow, Sp, D(2), Sp, Leq, Sp, Call("m", i));
        Formula coprime = Seq(
            Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            i, Sp, Lt, Sp, n, Sp, Land, Sp, j, Sp, Lt, Sp, n, Sp, Land, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Gcd, Open, Call("m", i), Comma, Sp, Call("m", j), Close,
            Sp, Eq, Sp, D(1));
        Formula correction = Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Sp, received, Comma, Sp,
            Open,
            x, Sp, Lt, Sp, range, Sp, Land, Sp, y, Sp, Lt, Sp, range, Sp, Land,
            HammingDistance(received, ResidueWord(m, n, x)), Sp, Leq, Sp, radius,
            Sp, Land, Sp,
            HammingDistance(received, ResidueWord(m, n, y)), Sp, Leq, Sp, radius,
            Close, Sp, Rightarrow, Sp, x, Sp, Eq, Sp, y);

        return Disp(Seq(
            Forall, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Forall, Sp, n, Comma, Sp, range, Comma, Sp, radius,
            Sp, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            Open, ordered, Close, Sp, Land, Sp,
            Open, positive, Close, Sp, Land,
            RowBreak, Grp(),
            Open, coprime, Close, Sp, Land, Sp,
            D(2), Sp, Leq, Sp, range, Sp, Land,
            RowBreak, Grp(),
            Open, correction, Close,
            RowBreak, Grp(),
            Rightarrow, Sp,
            Call("MinDistanceAtLeast", m, n, range, requiredDistance), Sp, Land,
            RowBreak, Grp(),
            range, Sp, Leq, Sp, Call("prefixProduct", m, prefixLength), Dot));
    }

    private static Formula ResidueWord(Formula m, Formula n, Formula x) =>
        Call("residueWord", m, n, x);

    private static Formula HammingDistance(Formula first, Formula second) =>
        Call("hammingDist", first, second);
}
