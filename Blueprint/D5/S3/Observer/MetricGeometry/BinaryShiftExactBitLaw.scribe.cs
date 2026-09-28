using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class BinaryShiftExactBitLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At error in [0,1), binary shift prediction through time H requires exactly H plus one bits.",
        H("Exact State and Bit Counts for the Binary Shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-predictor"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.HasFiniteHorizonPredictor"),
                H("Prediction through a prescribed horizon"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a deterministic controlled system F with observation o in a metric space, "
                    + "a predictor with state budget s consists of a nonempty finite state set S "
                    + "of cardinality at most s, an initialization e, total deterministic transitions G, "
                    + "and a readout h. For every initial state x and every action word w of length "
                    + "at most H, the distance between the predicted and true outputs is at most "
                    + "epsilon. The empty word is included. Transitions receive only the current "
                    + "state and action; readout receives only the state. Neither receives the time "
                    + "or a new observation. The predictor may depend on H and epsilon."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("binary-observation"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binaryObservation"),
                H("The leading bit as a sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An actual state is an infinite binary sequence indexed by the natural numbers. "
                    + "False represents zero and true represents one. The observation is minus one "
                    + "raised to the leading bit: zero gives one, and one gives minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exact-binary-shift-bit-law"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/BinaryShiftExactBitLaw.binary_shift_exact_bit_law"),
                H("The exact minimum state and bit counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F be the left shift, so that coordinate j after one step is the old "
                        + "coordinate j plus one. For every natural horizon H and every real error "
                        + "epsilon with zero less than or equal to epsilon and epsilon less than one, "
                        + "the least achievable autonomous state budget is 2^(H+1). Its ceiling "
                        + "base-two logarithm, expressed by Nat.clog, is H+1. The action alphabet "
                        + "is a singleton, so the transitions are autonomous. Predictor outputs "
                        + "may be arbitrary real numbers. Both H equal to zero and epsilon equal "
                        + "to zero are included.")),
                    Paragraph(Text(
                        "For the upper bound, store the first H+1 bits. Read the sign of the first "
                        + "bit, shift left at each step, and append zero. Induction on the number "
                        + "of steps shows that each remaining coordinate equals the corresponding "
                        + "original coordinate. Thus every readout through time H is exact, using "
                        + "2^(H+1) states and no additional clock.")),
                    Paragraph(Text(
                        "For the lower bound, extend every prefix of length H+1 by zeros. If two "
                        + "different prefixes had the same initialized state, their predicted "
                        + "outputs would coincide at a coordinate where their true signs differ. "
                        + "The true outputs there have distance two, while the triangle inequality "
                        + "bounds that distance by twice epsilon, which is strictly less than two. "
                        + "Initialization is therefore injective on all prefixes. Counting them "
                        + "gives the lower bound, and the ceiling logarithm of a power of two "
                        + "gives the exact bit count."))),
                DescribeRole.Theorem))));
}
