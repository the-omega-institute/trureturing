using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class ClassicalFiberBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite deterministic local-fiber models have exact absolute CHSH bound two.",
        H("Exact Classical Local-Fiber CHSH Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-classical-local-fiber-chsh-bound-is-exactly-two"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/ClassicalFiberBound.classical_chsh_bound_is_exact"),
                H("The classical local-fiber CHSH bound is exactly two"),
                StatementSource.FromAuthor(Disp(Seq(
                    Max, Underscore, Grp(Mathrm, Grp(F.Id("local"))), Sp,
                    Vert, Sp, F.Id("S"), Underscore, Grp(Mathrm, Grp(F.Id("cl"))),
                    Open, Mu, Close, Vert, Eq, D(2), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Fiber be finite. A deterministic local model assigns Boolean answer " +
                        "tables a0 and a1 to Alice and b0 and b1 to Bob, all depending only on " +
                        "the same hidden fiber address. Reading false and true as minus one and " +
                        "plus one, respectively, the pointwise CHSH value is a0*b0 + a0*b1 + " +
                        "a1*b0 - a1*b1. For nonnegative weights mu summing to one, classicalCHSH " +
                        "is the finite sum of mu times this pointwise value.")),
                    Paragraph(Text(
                        "The declaration classical_chsh_abs_le_two proves that every such weighted " +
                        "model has absolute value at most two. Its pointwise upper bound invokes " +
                        "mathlib's CHSH_inequality_of_comm on the four real answer values. Flipping " +
                        "both Alice answers and invoking the same theorem supplies the lower bound; " +
                        "finite convexity then transports both inequalities through the weights.")),
                    Paragraph(Text(
                        "The companion declaration classical_chsh_eq_two_exists takes all four " +
                        "answer tables constantly true and obtains value two from weight " +
                        "normalization. The stated IsGreatest certificate combines that witness " +
                        "with the absolute upper bound. Thus, when the hidden address is read as " +
                        "the shared local variable, the classical fiber bound is exactly 2.0.")),
                    Paragraph(Text(
                        "For contrast only, CHSHWitness.bell_chsh_value is the already frozen " +
                        "finite quantum witness with value two times square root two. This module " +
                        "does not reprove that value or a quantum upper bound, and it introduces " +
                        "no infinite fiber, measure-theoretic generalization, or general theory of " +
                        "Bell inequalities."))),
                DescribeRole.Theorem))));
}
