using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class GlobalPresetObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/GlobalPresetObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One original preset stream cannot acquire unequal nonempty even interior supports in two blocks.",
        H("The original GLOBAL contract and a two-block obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("global-preset-selector"),
                DeclarationHandle.Create(Owner + "presetSelector"),
                H("One literal stream with local stopping"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A stop function receives only the free initial output and this source's chronological archive. If it returns no label, the selector emits the next word of one fixed stream, indexed by the number of blocks actually emitted. Every still-running archive in both free-value fibres uses that same stream."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-global-preset-feasible"),
                DeclarationHandle.Create(Owner + "OriginalPresetFeasible"),
                H("Correct bounded execution on all actual INITIAL histories"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Feasibility supplies a stream and stop function whose selected words respect the chosen original alphabet. Initial bottom returns its fixed target label freely. For every actual finite AllowedBlock history, the original scanner and execute recursion must return the target of that history's immutable INITIAL record with fee at most the given budget. Full blocks, including rejection blocks, are charged. The controller receives no original history length, phase, inherited tail or interior observation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-global-two-block-obstruction"),
                DeclarationHandle.Create(Owner + "original_global_two_block_obstruction"),
                H("Unequal even interior supports require more than two blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least five, put k=2m-2 and take the full phase group ZMod(k+1). Define j=-theta_INITIAL modulo k+1, using the standard representative 0 through k, where theta_INITIAL is the INITIAL record phase. In each free-value fibre choose a nonempty even support H(v) in this j coordinate, contained in the representative interval 2 through m-1, with the two supports unequal. Choose arbitrary labels A(v) and B(v), unequal separately in each fibre, and any immutable target such that, for every inherited tail 0<=s<k, its live value at the INITIAL record (v,-j,s) is B(v) when j belongs to H(v) and A(v) otherwise. Under either original alphabet this target has no feasible GLOBAL execution with budget two. Cross-value label coincidences and the bottom label are unrestricted.")),
                    Paragraph(Text(
                        "The native bridge compares two actual INITIAL sources with equal free value and tail zero. Equality of both scheduled literal charges makes their acquired archives equal at every actually executed step. A stop at the root or after the first word therefore returns the same label; if they continue, rejection is simultaneous because legality depends only on the common tail and literal bits. The second charge is a mathematical function of the preset word. It does not supply an observation to a source that has stopped.")),
                    Paragraph(Text(
                        "Every second literal charge has zero total parity and vanishes on the interior support interval 2 through m-1 in the same negative INITIAL-phase coordinate j=-theta_INITIAL modulo k+1. An even target mask constant on the two response cells with second charge zero is either zero or one canonical mask. Applying this normal form to both value fibres forces one support empty or the supports equal, contradicting the hypotheses.")),
                    Paragraph(Text(
                        "This proves the lower obstruction in the internal-even-support classification. It does not construct a three-block stream, prove its upper bound, or claim the full zero/one/three classification. The parity argument is elementary finite-field algebra; no literature novelty or priority claim is made."))),
                DescribeRole.Theorem))));
}
