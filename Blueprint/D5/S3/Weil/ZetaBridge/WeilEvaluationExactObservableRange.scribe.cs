using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilEvaluationExactObservableRangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilEvaluationExactObservableRange.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite scalar even Weil observer reaches exactly the reflection-even, multiplicity-constant vectors; multiplicity replication preserves its readout kernel.",
        H("Exact Weil Observable Range"),
        Blocks(
            Describe.Lean(DescribeId.Create("weil-exact-index-observer-range"),
                DeclarationHandle.Create(Prefix + "finiteWeilIndexEvaluation_range_iff"),
                H("Reflection-evenness is sufficient and necessary"),
                StatementSource.FromAuthor(Disp(F.Id("exists actual Weil test with index readout v iff v is reflection even"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extend the finite window assignment by zero. Reflection closure preserves compatibility. The existing finite even interpolation theorem then supplies an actual compact smooth test."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-exact-expanded-observer-range"),
                DeclarationHandle.Create(Prefix + "finiteWeilCoordinateEvaluation_range_iff"),
                H("Exact image in multiplicity-expanded coordinates"),
                StatementSource.FromAuthor(Disp(F.Id("w is reachable iff w is fiber constant and its collapse is reflection even"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual positive analytic multiplicities provide one copy for collapse. Expansion and collapse are inverse on the fiber-constant subspace."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-replication-no-intrinsic-kernel-escape"),
                DeclarationHandle.Create(Prefix + "no_intrinsic_kernel_escape_from_multiplicity_replication"),
                H("Redundant copies create no semantic information gain"),
                StatementSource.FromAuthor(Disp(F.Id("no two original Weil-test states agree in index readout and differ in replicated readout"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state arena remains all WeilTestFunction values. These are kernel-equality statements on an infinite arena. No finite collision probability, artificial truth-conditioned state subtype, or primitive-law admission is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-mixed-exact-reduced-factorization"),
                DeclarationHandle.Create(Prefix + "truncatedZeroSum_mixed_eq_reducedMirrorForm"),
                H("Mixed Weil form factors through the exact range"),
                StatementSource.FromAuthor(Disp(F.Id("truncatedZeroSum(g * involution(h)) = reducedMirrorForm(E(g), E(h))"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The off-diagonal identity uses the existing mirror and convolution owners. Analytic multiplicity appears once as a weight. Kernel checking and admission remain separate verification obligations."))),
                DescribeRole.Theorem)), []));
}
