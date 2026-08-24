using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class SingleSampleLawNonimplicationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula boolean = F.Id("Bool");
        Formula channel = F.Id("K");
        Formula coupling = F.Id("gamma");
        Formula sample = F.Id("omega");
        Formula leftState = F.Id("false");
        Formula rightState = F.Id("true");
        Formula pmf = Call("PMF", boolean);
        Formula pair = Call("Prod", boolean, boolean);
        Formula leftLaw = Apply(channel, leftState);
        Formula rightLaw = Apply(channel, rightState);
        Formula leftSample = Apply(F.Id("fst"), sample);
        Formula rightSample = Apply(F.Id("snd"), sample);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp, channel, Colon, Sp, boolean, Sp, To, Sp, pmf,
            Comma, RowBreak, Grp(),
            Exists, Sp, coupling, Colon, Sp, Call("PMF", pair), Comma, Sp,
            sample, Colon, Sp, pair, Comma, RowBreak, Grp(),
            Call("map", F.Id("fst"), coupling), Sp, Eq, Sp, leftLaw,
            Sp, Land, RowBreak, Grp(),
            Call("map", F.Id("snd"), coupling), Sp, Eq, Sp, rightLaw,
            Sp, Land, RowBreak, Grp(),
            Apply(coupling, sample), Sp, Neq, Sp, D(0), Sp, Land, Sp,
            leftSample, Sp, Eq, Sp, rightSample, Sp, Land, RowBreak, Grp(),
            leftLaw, Sp, Neq, Sp, rightLaw, Sp, Land, Sp,
            leftState, Sp, Neq, Sp, rightState, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "One supported coupled equality need not identify either laws or states.",
            H("Single-Sample Law Nonimplication"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("single-coupled-sample-does-not-determine-law-or-state"),
                    DeclarationHandle.Create(
                        "D5/S3/Observer/ProbabilisticClosure/"
                            + "SingleSampleLawNonimplication."
                            + "single_coupled_sample_does_not_determine_law_or_state"),
                    H("One coupled sample identifies neither law nor state"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The public witnesses form a discrete stochastic channel K on Bool, "
                                + "a joint probability mass gamma, and one sampled pair omega. "
                                + "The first two equations certify that gamma has the channel laws "
                                + "at false and true as its two marginals.")),
                        Paragraph(Text(
                            "The explicit pair omega has nonzero gamma mass and equal coordinates, "
                                + "so it is a genuinely possible equal-output observation rather "
                                + "than a zero-mass point.")),
                        Paragraph(Text(
                            "Nevertheless, the two marginal laws are publicly unequal and the two "
                                + "source states are publicly distinct. Both nonimplication clauses "
                                + "therefore hold in the same coupled countermodel."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
