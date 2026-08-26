using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class WorstCaseDepthInformationLowerBoundDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-branch adaptive protocols have at most exponentially many leaves, forcing "
            + "the ceiling-logarithmic worst-case identification depth.",
        H("Worst-Case Depth Information Lower Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adaptive-leaf-count-le-pow"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "adaptive_leaf_count_le_pow"),
                H("A bounded-depth tree has at most exponentially many leaves"),
                StatementSource.FromAuthor(LeafCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction bounds each child subtree by B^d. Prefixing by one of the B "
                        + "answers and taking their union gives at most B^(d+1) leaves; a "
                        + "root leaf under unused budget uses the explicit premise 1 <= B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-identification-card-le-pow"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "exact_identification_card_le_pow"),
                H("Exact identification injects states into budgeted leaves"),
                StatementSource.FromAuthor(ExactCardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exactness makes the transcript map injective. Finite-cardinality "
                        + "monotonicity and the leaf count yield the state bound B^h."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("worst-case-depth-information-lower-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "worst_case_depth_information_lower_bound"),
                H("Worst-case exact depth is at least the upper logarithm"),
                StatementSource.FromAuthor(DepthLowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named adaptive depth is the least depth at which exact recognition "
                        + "exists. Its exact protocol gives |X| <= B^D, and mathlib's upper-log "
                        + "adjunction yields clog B |X| <= D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-branching-factor-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "positive_branching_factor_is_necessary"),
                H("Positive branching is necessary for the budget-depth count"),
                StatementSource.FromAuthor(PositiveBranchingNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At B=0, a zero-round protocol exactly identifies Unit and has depth at "
                        + "most one. Its single root leaf cannot satisfy 1 <= 0^1, giving the "
                        + "required concrete counterexample."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("empty-and-singleton-depth-zero-audit"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_and_singleton_depth_zero_audit"),
                H("Empty and singleton carriers need no questions"),
                StatementSource.FromAuthor(EmptySingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty transcript is injective on Empty and Unit. Their cardinalities "
                        + "are zero and one, and mathlib assigns upper logarithm zero to both."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("unary-exact-identification-card-le-one"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "unary_exact_identification_card_le_one"),
                H("Unary branching identifies at most one state"),
                StatementSource.FromAuthor(UnaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For B=1 every transcript type has cardinality one, independently of "
                        + "depth. An injective transcript therefore permits at most one state."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("binary-exact-identification-depth-lower-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "binary_exact_identification_depth_lower_bound"),
                H("Binary branching gives the standard base-two lower bound"),
                StatementSource.FromAuthor(BinaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Specializing the fixed branching factor to two gives the usual ceiling "
                        + "binary logarithm lower bound for every exact protocol."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("zero-depth-exact-identification-card-le-one"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "zero_depth_exact_identification_card_le_one"),
                H("Depth zero identifies at most one state"),
                StatementSource.FromAuthor(ZeroDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Without asking a question there is only the empty transcript. Exact "
                        + "recognition therefore forces the state carrier to be a subsingleton."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("constant-zero-readout-not-exact-on-bool"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_zero_readout_not_exact_on_bool"),
                H("A constant readout cannot distinguish Boolean states"),
                StatementSource.FromAuthor(ConstantReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every reachable question returns zero on both Boolean states, so their "
                        + "transcripts agree at every depth and exactness is impossible."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("full-transcript-space-attains-leaf-bound"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "full_transcript_space_attains_leaf_bound"),
                H("The exponential leaf bound is attained"),
                StatementSource.FromAuthor(EqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take states to be all B-valued transcripts of length h and ask for one "
                        + "coordinate each round. The identity transcript is injective and the "
                        + "state cardinality is exactly B^h."))),
                DescribeRole.Lemma))));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula LeafCountFormula()
    {
        Formula protocol = F.Id("pi");
        Formula branching = F.Id("B");
        Formula depth = F.Id("h");
        return Disp(Seq(
            D(1), Sp, Leq, Sp, branching, Sp, Implies, Sp,
            Call("card", Call("adaptiveLeaves", protocol)), Sp, Leq, Sp,
            Power(branching, depth), Dot));
    }

    private static Formula ExactCardinalityFormula()
    {
        Formula state = F.Id("X");
        Formula readout = F.Id("q");
        Formula branching = F.Id("B");
        Formula depth = F.Id("h");
        return Disp(Seq(
            D(1), Sp, Leq, Sp, branching, Sp, Land, Sp,
            Call("ExactAtDepth", readout, depth), Sp, Implies, Sp,
            Call("card", state), Sp, Leq, Sp, Power(branching, depth), Dot));
    }

    private static Formula DepthLowerBoundFormula()
    {
        Formula state = F.Id("X");
        Formula readout = F.Id("q");
        Formula branching = F.Id("B");
        return Disp(Seq(
            D(1), Sp, Leq, Sp, branching, Sp, Land, Sp,
            Call("Identifiable", readout), Sp, Implies, Sp,
            Call("clog", branching, Call("card", state)), Sp, Leq, Sp,
            Call("adaptiveIdentificationDepth", readout), Dot));
    }

    private static Formula PositiveBranchingNecessaryFormula()
    {
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("q"), D(1)), Sp, Land, Sp, Neg,
            Open, D(1), Sp, Leq, Sp, Power(D(0), D(1)), Close, Dot));
    }

    private static Formula EmptySingletonFormula()
    {
        Formula branching = F.Id("B");
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("qEmpty"), D(0)), Sp, Land, Sp,
            Call("ExactAtDepth", F.Id("qUnit"), D(0)), Sp, Land, Sp,
            Call("clog", branching, D(0)), Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Call("clog", branching, D(1)), Sp, Eq, Sp, D(0), Dot));
    }

    private static Formula UnaryFormula()
    {
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("q"), F.Id("d")), Sp, Implies, Sp,
            Call("card", F.Id("X")), Sp, Leq, Sp, D(1), Dot));
    }

    private static Formula BinaryFormula()
    {
        Formula stateCard = Call("card", F.Id("X"));
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("q"), F.Id("d")), Sp, Implies, Sp,
            Call("clog", D(2), stateCard), Sp, Leq, Sp, F.Id("d"), Dot));
    }

    private static Formula ZeroDepthFormula()
    {
        return Disp(Seq(
            Call("ExactAtDepth", F.Id("q"), D(0)), Sp, Implies, Sp,
            Call("card", F.Id("X")), Sp, Leq, Sp, D(1), Dot));
    }

    private static Formula ConstantReadoutFormula()
    {
        return Disp(Seq(
            Neg, Call("ExactAtDepth", Call("constantZero", D(2)), F.Id("h")), Dot));
    }

    private static Formula EqualityFormula()
    {
        Formula branching = F.Id("B");
        Formula depth = F.Id("h");
        Formula transcriptSpace = Call("TranscriptSpace", branching, depth);
        return Disp(Seq(
            Call("card", transcriptSpace), Sp, Eq, Sp, Power(branching, depth),
            Sp, Land, Sp,
            Call("ExactAtDepth", Call("coordinateReadout", transcriptSpace), depth),
            Dot));
    }
}
