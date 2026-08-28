using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class PrefixLawCompletionSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/PrefixLawCompletionSeparation."
            + "finite_prefix_infinite_completion_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite prefix of an explicit Bernoulli observation system has equivalent laws, "
            + "while the completed laws are mutually singular.",
        H("Prefix-Law and Completion Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("prefix-law-equivalence-completion-singularity"),
            DeclarationHandle.Create(Declaration),
            H("Finite-prefix laws are equivalent but completions are singular"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation system is the canonical pair of independent Boolean "
                        + "product laws with success probabilities one third and two thirds. "
                        + "Prefixes use finiteTranscript on those same completed laws.")),
                Paragraph(Text(
                    "For every finite prefix length, each mapped law is absolutely continuous "
                        + "with respect to the other.")),
                Paragraph(Text(
                    "The canonical empirical-mean event separates the two completed laws and "
                        + "therefore witnesses their mutual singularity."))),
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
