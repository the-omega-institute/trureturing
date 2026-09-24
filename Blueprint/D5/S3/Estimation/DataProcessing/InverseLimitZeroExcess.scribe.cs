using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InverseLimitZeroExcessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One common cut across all levels.",
        H("One common cut across all levels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-excess-levels"),
                DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.zero_excess_iff_all_levels"),
                H("One common cut across all levels"),
                StatementSource.FromAuthor(Disp(Seq(Call("zeroExcess", F.Id("y")), Sp, Iff, Sp, Forall, Sp, F.Id("l"), Comma, Sp, Call("zeroExcess", Call("project", F.Id("l"), F.Id("y")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let adjacent alphabet maps commute with the given permutations. Applying the permutations coordinatewise defines a permutation of the actual inverse-limit thread space.")),
                    Paragraph(Text("A tuple of threads is one-cut if and only if every level projection is one-cut. The sets of admissible cuts are nonempty finite decreasing sets. Their common element supplies one cut valid at every level, and coordinates separate threads.")),
                    Paragraph(Text("The exact failure-count characterization consequently makes completed zero excess equivalent to zero excess at every level. Neither surjectivity nor finiteness of the alphabets is needed for this pointwise statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("expected-zero-excess"),
                DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.expected_excess_zero_iff_all_levels"),
                H("Expected excess and projected laws"),
                StatementSource.FromAuthor(Disp(Seq(Call("expectedExcess", F.Id("Q")), Sp, Eq, Sp, D(0), Sp, Iff, Sp, Forall, Sp, F.Id("l"), Comma, Sp, Call("expectedExcess", Call("push", F.Id("l"), F.Id("Q"))), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On finite discrete Borel alphabets, the cycle excess is measurable on the space of tuples of threads. For any measure on this space, its nonnegative expected excess is zero exactly when every actual projected law has zero expected excess.")),
                    Paragraph(Text("A nonnegative measurable function has zero integral exactly when it vanishes almost everywhere. The pointwise common-cut characterization and a countable intersection of full-measure events establish both directions. The measure need not be a probability, and the excess sequence is not asserted to be monotone."))),
                DescribeRole.Theorem))));
}
