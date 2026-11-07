using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Energy;

internal sealed class OriginalWordEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The one seed-parametrized normal-word recurrence on the original lattice carrier.",
        H("Arbitrary-charge normal-word propagation"),
        Blocks(
            Paragraph(Text("This support module contains private consumed proof components. A numerical seed bounds the actualField(D,a) coefficient between nonnegative grades E,F<=M by K*(M+1)^B times the literal original norm. The conclusion for wordField(D,a,omega) is K*wordConstant(omega)*(M+1)^(B+wordWeight(omega)+length(omega)). This seed is discharged by actual_zero and identity_modes in the neutral prerequisite, and by the shared pre-relaxation charged estimate in the all-state consumer. It is not a hypothesis of either public endpoint.")),
            Paragraph(Text("word_charge and word_off_energy, together with the existing charge_energy_add identity, give the genuine total output grade E+chargeEnergy(D,a)+wordWeight(omega)-n-1. The left intermediate grade is F-q-r-1 and vanishes when negative. The right derivative coefficient is zero strictly for q<r; q=r is retained. Only after removing that strip is the right intermediate grade E-q+r converted to a natural grade, with 0<=E-q+r<=E. Thus every surviving recursive endpoint stays <=M. The exact finite ranges are F+1 and E+r+1.")),
            Paragraph(Text("The existing derivative coefficient bound A(r)*(M+1)^r, original mixed-state current bound sqrt(3*G(i,i))*(M+1), and total count <=(r+2)*(M+1) close the same recurrence for wordConstant. No factors are commuted and neither contractions nor non-diagonal interference are discarded. This module contains the only induction proving the word norm estimate; no separate charged or neutral copy is retained. All existing supplier attributions remain in place, and these helpers carry no independent novelty claim."))),
        []));
}
