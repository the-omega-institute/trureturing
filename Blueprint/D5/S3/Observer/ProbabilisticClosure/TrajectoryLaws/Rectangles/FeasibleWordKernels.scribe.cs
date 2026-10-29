using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles;

internal sealed class FeasibleWordKernelsDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Entry(string id, string selector, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/FeasibleWordKernels." + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasible original word kernels", H("Feasible original word kernels"),
        Blocks(
            Entry("message", "message", "Original word likelihood with an external message",
                "For an original binary edge presentation theta, an n-letter emitted word w and a terminal vector z, message is the original word matrix multiplied by z. Arbitrary nonnegative z are permitted, including zero coordinates. An empty word leaves z unchanged.", DescribeRole.Definition),
            Entry("transition", "transition", "A normalized original edge on feasible rows",
                "For an emitted bit x and a nonnegative next message z, the transition from s to t is M(x)(s,t) times z(t), divided by the original message M(x)z at s. A zero denominator gives a zero row under real division. Only rows with positive denominator are used as conditional probability rows.", DescribeRole.Definition),
            Entry("forward-product", "forwardProduct", "Chronological matrix product",
                "Before each edge, compute its remaining original word likelihood from the same terminal message. Multiply the resulting normalized transition matrices in chronological order. The empty product is the identity. The construction does not replace structural zeros by positive entries.", DescribeRole.Definition),
            Entry("forward-path", "forwardPath", "Chronological probability of a hidden path",
                "For a specified original hidden path, multiply the same suffix-normalized edge transitions along that path. The product has value one at word length zero. Intermediate zero messages remain in the construction, and no condition requires them all to be positive.", DescribeRole.Definition),
            Entry("feasible-word-product", "feasible_word_product", "The product is the original word kernel on its feasible support",
                "For every original word, every nonnegative terminal vector z and every state s whose word likelihood is positive, the matrix product from s to t equals the original word entry from s to t times z(t), divided by the word likelihood at s. Its row sums to one and gives zero mass to every endpoint where z is zero. The weighted identity used to obtain this formula holds even when the initial word likelihood is zero. Its induction cancels a denominator only after proving that a zero sum of nonnegative edge-message contributions makes each such contribution zero. Thus no globally invertible diagonal message matrix is needed.", DescribeRole.Theorem),
            Entry("starting-record", "startingRecord", "The actual word and future with a retained initial hidden state",
                "At integer time t, startingRecord fixes H(t) to s and fixes the original emitted word followed by a finite future word. All hidden coordinates after the initial state are unobserved. The event belongs to the same original joint law.", DescribeRole.Definition),
            Entry("actual-conditioned-word-path", "actual_conditioned_word_path", "Actual conditional hidden-path probabilities",
                "Let J be any probability measure satisfying the original marked-cylinder identities of theta. Fix an integer start t, an m-edge hidden path h, its emitted word w, and a following n-letter emitted word v. If startingRecord has positive J likelihood, then the J mass of the specified hidden and emitted m-edge cylinder together with v, divided by the J mass of startingRecord, equals forwardPath with terminal message equal to the original likelihood of v from each endpoint. The original cylinder factorization supplies both masses. The weighted path identity then yields the chronological product without an assumption that intermediate messages or stationary state masses are everywhere positive. The event at m zero is retained, and n zero supplies the constant terminal message one. This statement identifies an actual finite conditional probability under J, rather than postulating a conditional table.", DescribeRole.Theorem),
            Paragraph(Text("On a positive-weight closed hidden class C, use nativeComponent and component_restriction to retain the original restricted matrices and original conditioned law, with state carrier C. The terminal message for the left comparison is the original A times the future word likelihood. The construction supplies the normalized word-product relation for this message, and permits its zero coordinates. The formulas for visible extra past, the reverse conditional kernels, the center-bit readouts, rectangular minorization and the ordered half-line completion are separate assertions.")))));
}
