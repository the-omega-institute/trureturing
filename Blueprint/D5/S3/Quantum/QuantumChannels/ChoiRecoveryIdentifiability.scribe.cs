using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class ChoiRecoveryIdentifiabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An invertible fixed preparation constrains arbitrary CPTP recovery by the full normalized input-Choi defect.",
        H("Choi Recovery and Statistical Identifiability"),
        Blocks(Describe.Lean(
            DescribeId.Create("arbitrary-cptp-choi-bridge"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/ChoiRecoveryIdentifiability.arbitrary_cptp_choi_bridge"),
            H("The actual quantum recovery bridge"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "All six roles Ai, Ao, Bi, Bo, Ci and Co have the same arbitrary positive "
                    + "finite dimension d. The recovery R from BiBo to BiBoCiCo is any canonical "
                    + "QuantumChannel, hence completely positive and trace preserving on the full "
                    + "complex matrix algebra. M is nonnegative and doubly stochastic, N M is "
                    + "the identity, and differences within every column of N are bounded above by L.")),
                Paragraph(Text(
                    "omega is the identity divided by d, E_x is the computational basis projector, "
                    + "and alpha_x is the diagonal matrix with column x of M. The fixed initializer "
                    + "is the average over x of alpha_x on Ai, E_x on Ao, omega on Bi and E_x on Bo. "
                    + "The CP-positive output sum equals the entrywise id tensor R action on this "
                    + "initializer. The outputState and targetState use the existing DensityState carrier.")),
                Paragraph(Text(
                    "The target has uniform Ai and Bi, a uniform common label Ao=Bo=Ci, and Co=0. "
                    + "Its full input marginal is omega on each of Ai, Bi and Ci. inputMarginal "
                    + "traces Ao, Bo and Co while retaining every complex input entry. Its full entry "
                    + "formula, positivity and trace one are included in the theorem. inputDefect "
                    + "is half the canonical trace norm of this full marginal minus the uniform "
                    + "input matrix. No reduced or measured quantity replaces this definition.")),
                Paragraph(Text(
                    "For each initializer label x, conditional is the entire Ci marginal of "
                    + "R(omega tensor E_x). It is positive semidefinite with trace one. "
                    + "Tracing Bi, Bo and Co from the actual output gives the average of "
                    + "alpha_x tensor E_x tensor conditional_x, including off-diagonal Ci entries. "
                    + "Born probabilities P_xc are its real diagonal entries and form a row-stochastic matrix.")),
                Paragraph(Text(
                    "Measuring Ai and Ci after tracing Bi gives defect equal to the sum of "
                    + "absolute entries of M P-Pi divided by 2d. A triangle inequality on grouped "
                    + "diagonal entries and the Jordan decomposition bound this by the FULL "
                    + "inputDefect. The generic inverse-preparation estimate therefore controls "
                    + "trace(P)-1 by L times this full defect after normalization.")),
                Paragraph(Text(
                    "The equality event is Ao=Ci. Its target probability is one and its actual "
                    + "probability is trace(P)/d. The zero-mass pairing estimate and the quantum "
                    + "Jordan mass bound its probability gap by full output trace distance D. "
                    + "Consequently D+L delta is at least 1-1/d. Exact full input normalization "
                    + "also gives complete matrix equations sum_x M_ax conditional_x=omega. "
                    + "Multiplication by N forces every conditional_x to equal omega, including all coherences.")),
                Paragraph(Text(
                    "For the symmetric binary preparation, M has diagonal entries (1+e)/2 "
                    + "and off-diagonal entries (1-e)/2, with 0<e<1. The inverse has diagonal "
                    + "entries (1+e)/(2e) and off-diagonal entries (e-1)/(2e), so its column "
                    + "oscillation is 1/e. Substitution gives delta+e D at least e/2. "
                    + "Exact full input normalization forces the complete conditional matrices "
                    + "to be I/2 and D at least 1/2. These are applications of the general "
                    + "bridge, rather than separate formalization targets.")),
                Paragraph(Text(
                    "This is a fixed-initializer obstruction. It does not solve the full "
                    + "Liu-Wild recovery question or assert optimality of the entire error-defect "
                    + "curve. Changing the initializer, backtracking, joint reconstruction, "
                    + "or optimizing a different target is outside the theorem. No novelty claim is made."))),
            DescribeRole.Theorem))));
}
