using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ReadoutBlackwellAdapterDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ReadoutBlackwellAdapter.bayesRisk_mono_of_measurable_refinement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Measurable readout factorization becomes deterministic Blackwell "
            + "garbling and Bayes-risk monotonicity.",
        H("Readout Refinement as Blackwell Garbling"),
        Blocks(Describe.Lean(
            DescribeId.Create("readout-blackwell-adapter"),
            DeclarationHandle.Create(Declaration),
            H("Finer measurable readouts have no larger optimal Bayes risk"),
            StatementSource.FromAuthor(RiskMonotonicityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Measurable refinement augments the repository factorization preorder with the measurability required to form deterministic kernels.")),
                Paragraph(Text(
                    "Mathlib's deterministic-kernel composition identity turns the factor map into a Blackwell garbling from the finer readout to the coarse readout.")),
                Paragraph(Text(
                    "The existing repository Blackwell theorem then gives Bayes-risk monotonicity for every prior, measurable decision space, and ENNReal-valued loss."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/ConceptJoinUniversal")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk")),
        ]));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula RiskMonotonicityFormula()
    {
        Formula qc = new Formula.Subscript(F.Id("q"), F.Id("C"));
        Formula qd = new Formula.Subscript(F.Id("q"), F.Id("D"));
        Formula loss = F.Id("L");
        Formula prior = F.Id("mu");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, qc, Comma, Sp, qd, Comma, Sp, loss, Comma, Sp,
            prior, Colon, Sp,
            Call("MeasurableRefines", qc, qd), Sp, Rightarrow,
            RowBreak, Grp(),
            Call("bayesRisk", loss, Call("deterministic", qd), prior),
            Sp, Leq, Sp,
            Call("bayesRisk", loss, Call("deterministic", qc), prior), Dot,
            End, Grp(F.Id("gathered"))));
    }

}
