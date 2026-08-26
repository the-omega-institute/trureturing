using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentBoundary;

internal sealed class FinitePrefixInfiniteCompletionSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentBoundary/"
            + "FinitePrefixInfiniteCompletionSeparation."
            + "finite_prefix_infinite_completion_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite prefix of an explicit Bernoulli observation system has equivalent laws, "
            + "while the completed laws are mutually singular.",
        H("Finite-Prefix and Infinite-Completion Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-prefix-laws-are-equivalent-but-completions-are-singular"),
            DeclarationHandle.Create(Declaration),
            H("Finite-prefix laws are equivalent but completions are singular"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation system is the frozen pair of independent Boolean product "
                        + "laws with success probabilities one third and two thirds. Prefixes "
                        + "are obtained by the canonical finiteTranscript map from those same "
                        + "completed laws.")),
                Paragraph(Text(
                    "For every finite prefix length, both product laws have full support on the "
                        + "finite Boolean transcript space. Each mapped prefix law is therefore "
                        + "absolutely continuous with respect to the other.")),
                Paragraph(Text(
                    "On completed transcripts, the empirical-mean event from the frozen system "
                        + "has probability zero in the lower state and one in the upper state. "
                        + "That same event directly witnesses mutual singularity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula length = F.Id("m");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula falseLaw = Call("stateLaw", F.Id("false"));
        Formula trueLaw = Call("stateLaw", F.Id("true"));
        Formula prefix = Call("finiteTranscript", length);
        Formula falsePrefix = Call("map", prefix, falseLaw);
        Formula truePrefix = Call("map", prefix, trueLaw);

        return Disp(new Formula.Aligned([
            Seq(Open, Forall, Sp, length, Sp, InMacro, Sp, naturals, Comma),
            Seq(Call("AbsolutelyContinuous", falsePrefix, truePrefix), Sp, Land),
            Seq(Call("AbsolutelyContinuous", truePrefix, falsePrefix), Close, Sp, Land),
            Seq(Call("MutuallySingular", falseLaw, trueLaw), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula>
        {
            Operatorname, Grp(F.Id(name)), Open
        };
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
