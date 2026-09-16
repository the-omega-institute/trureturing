using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalReadoutOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalReadoutOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rotation error packets determine the exact weight cone for order-preserving numerical readouts.",
        H("Mechanical Readout Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-additive-readout"),
                DeclarationHandle.Create(Prefix + "weightedPrefix"),
                H("Additive numerical readout of actual letters"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite sum uses the existing lowerMechanicalLetter evaluated on a real slope and phase. The weight sequence is arbitrary and real-valued. At slopes in [0,1) each letter is a genuine binary observation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mechanical-readout-order-cone"),
                DeclarationHandle.Create(Prefix + "local_order_iff_decreasing_weights"),
                H("Exact local order-preservation criterion"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every fixed irrational slope in (0,1), and for every nonempty finite horizon m+1, the weighted readout is nondecreasing under all sufficiently small upward slope changes at every phase exactly when the weights decrease and the last weight is nonnegative. Necessity intersects an arbitrary proposed monotonicity radius with the actual geometric chamber, then constructs a phase in each nonempty swept interval. The realized adjacent exchanges force every weight drop, and the last-bit interval forces the terminal sign. Sufficiency proves the finite summation-by-parts identity on actual cumulative floors and uses their order. No arbitrary binary-pattern realizability or weight-order assumption is hidden in the forward direction. Summation by parts is prior mathematics. Infinite dyadic completion and the integrated error identities are ordinary consequences recorded separately in the theory."))),
                DescribeRole.Theorem))));
}
