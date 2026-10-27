using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalControlMarkedJumpDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original double-wall jump operators determine a normalized continuous marked law on each affine leg.",
        H("Original Continuous Marked Jump Law"),
        Blocks(Describe.Lean(
            DescribeId.Create("affine-marked-probability"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalControlMarkedJump.affine_marked_probability"),
            H("A complete marked probability law on an affine leg"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix c below one half and positive heights x,y below c. A positive duration h gives the actual height k(t)=x+(y-x)*t/h. The five probabilities are (k,c-k,1-2*c,c-k,k), with the last coordinate retaining original mode13. Both directions and the stationary case are included. A constant real control phase has zero transported phase. No common duration or speed bound is imposed.")),
                Paragraph(Text("The prepared input has middle amplitude sqrt(1-2*c). Each bottom amplitude is its positive probability square root times the negative exponential of its preparation angle plus an arbitrary common unknown phase. The two minus modes also carry the arbitrary integer parity factor. Thus every input of the original phase and parity family is retained, and its diagonal is exactly the original probability vector at x.")),
                Paragraph(Text("The actual hazard is the positive part of k prime divided by k, plus the positive part of minus k prime divided by c-k. Survival is defined by the exponential of minus the integral of this hazard. Integrating the appropriate logarithmic derivative gives x/k on an increasing leg, and (c-x)/(c-k) on a decreasing leg. The original mode jump rate is the hazard minus the derivative of log p_i(k). All five rates are nonnegative.")),
                Paragraph(Text("The successful operator is the original diagonal matrix with entries sqrt(S)*sqrt(p_i(k)/p_i(x)). The jump matrix is the absorbing row sqrt(g_i)*bra(i), multiplied by that successful matrix. Matrix action on the original prepared input gives squared absorbing amplitude g_i*S*p_i(k). Preparation phases cancel in this calculation; they are not chosen to simplify the input. The sum of the successful squared amplitudes is S.")),
                Paragraph(Text("Differentiating S*p_i(k) on a leg gives minus this mode density. Its integral is therefore p_i(x)-S(h)*p_i(y). Summing the five exact balances proves that the continuous failure mass is 1-S(h). The marked measure is the success atom of mass S(h), plus one density measure for every original mode on the entire continuous interval (0,h]. These measures have no failure atoms. Their total mass is one.")),
                Paragraph(Text("For every Borel set of records, the measure agrees with the sum of the actual squared Kraus outputs integrated over precisely its retained time and mode labels. The output space includes both terminal success and the complete continuous failure record. This is a finite-dimensional source-family statement. It makes no assertion about trace distance for arbitrary references or the common absorbing extension.")),
                Paragraph(Text("A repeated-prefix early and late construction additionally requires chronological assembly of these laws, equality of the literal duration2 prefix, the exact suffix clocks, disjoint suffix failure supports, the event supremum in the probability convention of total variation, and the fixed positive height gap. Those conclusions, their resource equalities and the inverse obstruction do not follow merely from the affine-leg statement."))),
            DescribeRole.Theorem))));
}
