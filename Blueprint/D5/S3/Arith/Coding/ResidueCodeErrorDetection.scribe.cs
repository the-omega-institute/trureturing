using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ResidueCodeErrorDetectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A code of minimum distance at least d detects every nonzero error of weight at most d - 1, and this guarantee is sharp.",
        H("Minimum-Distance Error Detection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("codewords-closer-than-the-minimum-distance-coincide"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeErrorDetection."
                        + "codeword_eq_of_hammingDist_lt"),
                H("Codewords closer than the minimum distance coincide"),
                StatementSource.FromAuthor(CodewordEqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose every distinct pair of words in a code is separated by at "
                            + "least d coordinates. If two codewords c and x have Hamming "
                            + "distance strictly below d, they cannot be distinct and hence "
                            + "must be the same word."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("minimum-distance-detects-errors-through-d-minus-one"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeErrorDetection."
                        + "detects_up_to_min_distance_minus_one"),
                H("Minimum distance detects errors through d minus one"),
                StatementSource.FromAuthor(DetectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c be a transmitted codeword and x the received word. Positive "
                            + "Hamming distance makes the error nonzero, while a distance at "
                            + "most d - 1 places x strictly inside the minimum-distance radius. "
                            + "If x were another codeword, the code's distance condition would "
                            + "force its distance from c to be at least d, a contradiction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-d-minus-one-detection-bound-is-sharp"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeErrorDetection."
                        + "detection_bound_is_sharp"),
                H("The d minus one detection bound is sharp"),
                StatementSource.FromAuthor(SharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive d, take the two Boolean words of length d that are "
                            + "constantly false and constantly true. They differ in every "
                            + "coordinate, so their Hamming distance is exactly d, and the "
                            + "two-word code has minimum distance d. An error of weight d can "
                            + "therefore carry one valid codeword to the other."))),
                DescribeRole.Theorem))));

    private static Formula CodewordEqualityFormula()
    {
        Formula code = F.Id("C");
        Formula first = F.Id("c");
        Formula second = F.Id("x");
        Formula distance = F.Id("d");

        return Disp(Seq(
            Forall, Sp, code, Comma, Sp, first, Comma, Sp, second, Comma, Sp, distance,
            Comma, Sp, Open,
            MinimumDistance(code, distance), Sp, Land, Sp,
            first, Sp, InMacro, Sp, code, Sp, Land, Sp,
            second, Sp, InMacro, Sp, code, Sp, Land, Sp,
            HammingDistance(first, second), Sp, Lt, Sp, distance,
            Close, Sp, Rightarrow, Sp, second, Sp, Eq, Sp, first, Dot));
    }

    private static Formula DetectionFormula()
    {
        Formula code = F.Id("C");
        Formula sent = F.Id("c");
        Formula received = F.Id("x");
        Formula distance = F.Id("d");
        Formula errorWeight = HammingDistance(sent, received);

        return Disp(Seq(
            Forall, Sp, code, Comma, Sp, sent, Comma, Sp, received, Comma, Sp, distance,
            Comma, Sp, Open,
            MinimumDistance(code, distance), Sp, Land, Sp,
            sent, Sp, InMacro, Sp, code, Sp, Land, Sp,
            D(1), Sp, Leq, Sp, errorWeight, Sp, Land, Sp,
            errorWeight, Sp, Leq, Sp, distance, Sp, Minus, Sp, D(1),
            Close, Sp, Rightarrow, Sp,
            Neg, Sp, Open, received, Sp, InMacro, Sp, code, Close, Dot));
    }

    private static Formula SharpnessFormula()
    {
        Formula code = F.Id("C");
        Formula first = F.Id("c");
        Formula second = F.Id("x");
        Formula distance = F.Id("d");

        return Disp(Seq(
            Forall, Sp, distance, Sp, InMacro, Sp, NaturalNumbers(), Comma, Sp,
            D(0), Sp, Lt, Sp, distance, Sp, Rightarrow, Sp,
            Exists, Sp, code, Sp, Subseteq, Sp, BooleanWords(distance), Comma, Sp,
            Exists, Sp, first, Comma, Sp, second, Comma, Sp, Open,
            MinimumDistance(code, distance), Sp, Land, Sp,
            first, Sp, InMacro, Sp, code, Sp, Land, Sp,
            second, Sp, InMacro, Sp, code, Sp, Land, Sp,
            first, Sp, Neq, Sp, second, Sp, Land, Sp,
            HammingDistance(first, second), Sp, Eq, Sp, distance,
            Close, Dot));
    }

    private static Formula MinimumDistance(Formula code, Formula distance) =>
        Call("MinDistanceAtLeast", code, distance);

    private static Formula HammingDistance(Formula first, Formula second) =>
        Call("hammingDist", first, second);

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula BooleanWords(Formula length) =>
        Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace, Caret, Grp(length));
}
