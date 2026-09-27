using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.SymbolicStability;

internal sealed class SmoothFiniteMachineRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smooth local plateaus realize finite machines with exact decoding under bounded noise at every prefix.",
        H("Smooth Error Correction for Finite Symbolic Machines"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smooth-finite-machine-realization"),
                DeclarationHandle.Create("D5/S3/Observer/SymbolicStability/SmoothFiniteMachineRealization.smooth_finite_machine_realization"),
                H("One smooth realization for all words and all bounded disturbances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let S be a nonempty finite state set, A any action type, and Y any output type. Each action has an arbitrary deterministic transition on S, and each state has a prescribed output in Y. Let c assign code points in d-dimensional Euclidean space, with every pair of different states at distance at least Delta. Suppose 0 <= nu < r < R < Delta/2. In particular, this includes every finite action set and every state set with at least two elements whose minimum code distance is Delta.")),
                    Paragraph(Text("There exist globally continuously differentiable updates T, a total state decoder, and a total output readout. On each closed radius-r ball about c(i), every update T(a) is identically c(delta(a,i)); the decoder returns i and the readout returns y(i). Neither continuity of the decoder nor any structure on Y is required.")),
                    Paragraph(Text("A finite word consists of action and disturbance pairs. Its continuous trajectory applies each update and then adds that pair's disturbance; its symbolic trajectory applies the actions in the same order. For every such word whose disturbances have Euclidean norm at most nu, every initial point in the closed radius-r ball about any c(i), and every prefix length, the continuous trajectory remains within r of the corresponding symbolic code point. The same decoder and readout return exactly that symbolic state and its output, including at the empty prefix.")),
                    Paragraph(Text("Choose smooth bump functions equal to one on the radius-r balls and zero outside the radius-R balls. Separation makes all other bumps zero on each decoding ball. Adding their weighted target-code displacements to one fixed code point gives the updates. Each update resets the current ball exactly to its target center, so the next disturbance has distance at most nu < r from that center. Induction on the word preserves the decoding ball. This existence statement imposes no particular neural architecture, width, training method, or global contraction condition."))),
                DescribeRole.Theorem))));
}
