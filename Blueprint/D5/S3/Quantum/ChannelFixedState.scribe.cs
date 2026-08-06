using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class ChannelFixedStateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/ChannelFixedState",
            "Positive trace-preserving finite-dimensional matrix maps admit invariant states."),
        H("Invariant States of Finite-Dimensional Channels"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("positive-trace-preserving-matrix-maps-admit-invariant-states"),
                H("Positive trace-preserving matrix maps admit invariant states"),
                LeanTheorem("D5/S3/Quantum/ChannelFixedState.channel_fixed_state_exists"),
                Disp(Seq(
                    Forall, Sp, F.Id("n"), Comma, Esc,
                    Forall, Sp, Phi, Colon, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("n")), Open, Mathbb, Grp(F.Id("C")), Close,
                    Sp, To, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("n")), Open, Mathbb, Grp(F.Id("C")), Close,
                    Comma, Esc,
                    Open, Forall, Sp, Rho, Comma, Esc,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Phi, Open, Rho, Close, Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, Rho, Comma, Esc,
                    Operatorname, Grp(F.Id("tr")), Open, Phi, Open, Rho, Close, Close,
                    Eq, Operatorname, Grp(F.Id("tr")), Open, Rho, Close,
                    Close, Sp, Rightarrow, Sp,
                    Exists, Sp, Rho, Comma, Esc,
                    Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("tr")), Open, Rho, Close, Eq, D(1),
                    Sp, Land, Sp, Phi, Open, Rho, Close, Eq, Rho)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Let n be a nonempty finite index type. Every complex-linear endomorphism of the n-by-n complex matrices that preserves positive semidefiniteness and trace has a positive semidefinite trace-one fixed point. Complete positivity is not assumed. The proof starts from the normalized identity and forms the Cesaro averages of its forward orbit. Positivity and trace preservation keep every average in the state space; nonnegative eigenvalues summing to one bound the operator norm, so finite-dimensional compactness supplies a convergent subsequence. The difference between an average and its image is a telescoping endpoint term divided by the averaging length and therefore tends to zero, forcing the subsequential limit to be fixed. This is a linear-algebraic compactness proof and does not invoke Brouwer's fixed-point theorem. No repository literature note currently attests this standard channel fixed-state result, so provenance is conservatively recorded as repository-derived.")))))));
}
