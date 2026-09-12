using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalPastSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire past can leave a target-relevant ambiguity for every irrational mechanical slope.",
        H("Mechanical Past Separation and Sharp Prediction"),
        Blocks(
            Paragraph(Text(
                "Fix an irrational alpha strictly between zero and one. The lower and upper "
                + "traces are successive floor and ceiling differences of (t-m)*alpha at integer "
                + "times. Both are actual binary traces of the same rotation boundary orbit. "
                + "No finite observation graph or assumed splitting axiom defines these traces.")),
            Describe.Lean(
                DescribeId.Create("mechanical-exact-disagreement-support"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPastSeparation.disagree_iff"),
                H("The disagreement has exactly two sites"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Disagreement"), Open, F.Id("m"), Close,
                    Sp, Eq, Sp, OpenBrace, F.Id("m"), Sp, Minus, Sp, D(1),
                    Comma, F.Id("m"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonzero integer multiple of an irrational slope is not an integer. "
                    + "Ceiling therefore equals floor plus one away from the boundary, and the "
                    + "two corrections cancel. At times m-1 and m the words read 10 and 01, "
                    + "respectively. The source also proves binary values and shift covariance."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "PastEq(J) compares every J-sample window beginning at an integer time at most "
                + "zero; the current window includes samples 0 through J-1. SegmentEq(L,h) "
                + "compares every L-sample window beginning at times 0 through h. These are "
                + "word-sample lengths, not unproved identifications with Zeckendorf digit depths.")),
            Describe.Lean(
                DescribeId.Create("mechanical-whole-past-threshold"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPastSeparation.whole_past_prediction_iff"),
                H("Whole-past prediction has an exact coverage threshold"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("PredictableTriples"), Sp, Eq, Sp, OpenBrace,
                    Open, F.Id("J"), Comma, F.Id("L"), Comma, F.Id("h"), Close,
                    Sp, Colon, Sp, F.Id("L"), Sp, Plus, Sp, F.Id("h"),
                    Sp, Leq, Sp, F.Id("J"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive L, prediction holds for all boundary traces exactly when "
                        + "L+h is at most J. Sufficiency is a restriction of the current window "
                        + "and holds for arbitrary traces. Necessity chooses the explicit "
                        + "boundary m=L+h: the entire J-past agrees, while the last sample of "
                        + "the terminal L-window disagrees.")),
                    Paragraph(Text(
                        "This proves a general irrational mechanical theorem, not the complete "
                        + "infinite-digit Zeckendorf dictionary. Transport through that dictionary "
                        + "requires a separate Lean equivalence with endpoint conventions preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-infinite-past-residual"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/MechanicalPastSeparation.whole_past_kernel_not_target_kernel"),
                H("Every finite window depth has an infinite-past residual"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("J"), Comma, Sp,
                    F.Id("PastResidual"), Open, F.Id("J"), Close,
                    Sp, Eq, Sp, F.Id("nonempty")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There are two actual traces with equal complete J-pasts but different "
                    + "values at time J. Agreement resumes after the two-site crossing; this "
                    + "does not erase the difference in the earlier observed segment, and "
                    + "does not identify the two full bi-infinite traces."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Words/Mechanical/MechanicalBalance")),
        ]));
}
