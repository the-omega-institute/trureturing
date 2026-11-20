using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSAnalyticBranchSeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticBranchSeparation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module,
            "Distinct analytic graphs separate on a relatively open dense set.",
            "static-algebraic-identifiability",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Analysis.Analytic.Uniqueness")),
        H("Generic separation of analytic branches"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsanalyticbranchseparation-result"),
            DeclarationHandle.Create(Module + ".open_dense_compl_of_analytic_fiber_charts"),
            H("Generic separation of analytic branches"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "On a preconnected space, a locally finite analytic ambiguity relation has an open dense complement if its branches separate at one chart."))),
            DescribeRole.Theorem))));
}
