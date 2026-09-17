using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rotation bits determine order-preserving weights and an isometric geometric completion with exact finite-precision cost.",
        H("Mechanical Readout Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-additive-readout"),
                DeclarationHandle.Create(Prefix + "weightedPrefix"),
                H("Additive numerical readout of actual letters"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite sum uses the existing lowerMechanicalLetter evaluated on a real slope and phase. The weight sequence is arbitrary and real-valued. At slopes in [0,1), each letter is a genuine binary observation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mechanical-readout-order-cone"),
                DeclarationHandle.Create(Prefix + "local_order_iff_decreasing_weights"),
                H("Exact local order-preservation criterion"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every fixed irrational slope in (0,1), and for every nonempty finite horizon m+1, the weighted readout is nondecreasing under all sufficiently small upward slope changes at every phase exactly when the weights decrease and the last weight is nonnegative. Necessity intersects an arbitrary proposed monotonicity radius with the actual geometric chamber, then constructs a phase in each nonempty swept interval. The realized adjacent exchanges force each weight drop, and the last-bit interval forces the terminal sign. Sufficiency proves the finite summation-by-parts identity on actual cumulative floors and uses their order. No arbitrary binary-pattern realizability or weight-order assumption is hidden in the forward direction. Summation by parts is prior mathematics. Its shared actual-floor identity is also consumed by the geometric completion theorem in this same owner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-geometric-completed-readout"),
                DeclarationHandle.Create(Prefix + "geometricReadout"),
                H("Geometric completion of actual binary letters"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The infinite sum uses the actual mechanical letters with weights (1-r)*r^k. For r in [0,1), the main theorem proves convergence, integrability, and a uniform tail. Binary positional weighting is r=1/2; r=0 is included without a special-case assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mechanical-geometric-isometric-completion"),
                DeclarationHandle.Create(Prefix + "geometric_readout_isometric_completion"),
                H("Actual readout integration, L1 distance and mixed precision"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every r in [0,1) and slopes alpha,beta in [0,1), the completed readouts are integrable on the uniform unit phase interval, with a nonnegative pointwise truncation tail at most r^n. The finite integrated absolute distance is (1-r^n)*abs(beta-alpha), and the infinite distance is exactly abs(beta-alpha). If beta<=alpha, the mixed completed/finite error is exactly alpha-beta*(1-r^n). The proof integrates each actual shifted floor through its carry interval, derives every letter mean, shares the actual-floor summation-by-parts order argument, proves summability and tails by positive series comparison, and applies dominated convergence. No expectation, convergence, integrability, or distance formula is assumed. The result is a concrete integral identity, not a declaration that a single scalar sample decodes every infinite word."))),
                DescribeRole.Theorem))));
}
