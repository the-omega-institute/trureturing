using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Lattice;

internal sealed class LatticeChargePrecedenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice saturation and the physical suffix charge",
        H("Lattice saturation and the physical suffix charge"),
        Blocks(
            Describe.Lean(DescribeId.Create("lattice-saturation-suffix-precedence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Lattice/LatticeChargePrecedence.lattice_saturation_suffix_precedence"),
                H("One occurrence, one return, one suffix budget"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G>0 and H>0. Supply a permutation of all m physical labels, old values f in G times the integers, nonnegative charges q of positive total A, and new old-label values g=2f-q. The fresh label m has value A and is literally inserted at cut j. Retain both complete zero totals, every old prefix in [0,C], and every new prefix in [0,N]. Let nu have old value -H, positive charge, H in the same lattice, and H<=C<H+G.")),
                    Paragraph(Text("Write p=idxOf(nu), with zero-based positions. The old height immediately before nu is a lattice point in [H,C], so it is exactly H; immediately after nu it is zero. If the ear had not occurred, the new prefix ending at nu would be minus the already used charge, which is strictly negative. Thus j<=p, including insertion immediately before nu.")),
                    Paragraph(Text("The actual new prefix immediately before nu now has height 2H+A-Q_p. Its upper bound gives A-Q_p<=N-2H. The permutation and complete charge total identify A-Q_p with the charge sum of sigma.drop p, the suffix containing nu itself. Every distinct label delta with q_delta+q_nu>N-2H must precede nu. Nonnegative charges put both charges into this very same suffix if delta has not yet occurred. No favorable alternative cut, pre-placed delta, or numerical-value quotient is assumed.")),
                    Paragraph(Text("Strict saturation C<H+G and strict charge dominance are retained. The complete zero totals preserve the joint physical witness interpretation although the local order argument does not need them. This is a necessary-order theorem; it constructs no joint witness and leaves physical J and Circle C3.1 open. The proof reuses the original ear_prefix and sum_linear owners. No independent literature novelty is asserted."))),
                DescribeRole.Theorem)), []));
}
