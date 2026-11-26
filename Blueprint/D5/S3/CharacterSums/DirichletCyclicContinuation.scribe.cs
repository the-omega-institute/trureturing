using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletCyclicContinuationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/DirichletCyclicContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized cyclic analytic continuation",
        H("The normalized cyclic analytic continuation"),
        Blocks(
            Paragraph(Text("The selected length r may be any natural number at most "
                + "the order of chi; all selected positive powers are nonprincipal.")),
            Paragraph(Text("Use the entire normalized zeta factor and both Schwarz partners "
                + "of each nontrivial character power. The zeta weight is one; each partner "
                + "has half the original positive cyclic weight. The divided difference at "
                + "one removes the artificial singularity before division by s.")),
            Describe.Lean(DescribeId.Create("cyclic-continuation-laplace"),
                DeclarationHandle.Create(Module + "continuation_half_plane_laplace"),
                H("Agreement with the arithmetic transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The normalized zeta "
                    + "logarithmic derivative and its value at one account exactly for the "
                    + "double-pole and linear corrections in the arithmetic transform."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-actual-poles"),
                DeclarationHandle.Create(Module + "continuation_actual_poles"),
                H("The actual simple poles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Its residue is minus "
                    + "the positive weighted sum of actual analytic orders, divided by the "
                    + "zero times the zero minus one. The positive weighted multiplicity "
                    + "cannot cancel. The continuation is analytic away from these locally "
                    + "discrete zeros and has the stated simple principal part at each zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-zero-set-left-of-one"),
                DeclarationHandle.Create(Module + "actualZeros_re_lt_one"),
                H("Every actual factor zero is left of one"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For r at most the character order, every zero in the actual "
                    + "factor zero set has real part strictly less than one. The existing "
                    + "nonvanishing theorems apply to each factor and its Schwarz partner."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-real-residue-positive"),
                DeclarationHandle.Create(Module + "actual_real_residue_pos"),
                H("Real actual zeros give positive real residues"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At an actual zero z with zero imaginary part, the "
                    + "residue has positive real part and zero imaginary part. The zero "
                    + "lies between zero and one, so minus one divided by z(z-1) is "
                    + "positive; its weighted analytic multiplicity is positive as well."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-zeta-zero-in-actual-set"),
                DeclarationHandle.Create(Module + "zeta_zero_mem_actualZeros"),
                H("Ordinary zeta zeros occur in the actual factor set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every zero of ordinary zeta with positive real "
                    + "part belongs to the actual zero set. Nonvanishing of the "
                    + "totalized zeta value at one supplies z different from one "
                    + "inside the proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cyclic-member-zero-in-actual-set"),
                DeclarationHandle.Create(Module + "member_zero_mem_actualZeros"),
                H("Cyclic-power zeros occur in the actual factor set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every index j in Fin(r-1), a zero of the "
                    + "L-function of chi to the power j+1 with positive real part "
                    + "belongs to the actual zero set."))), DescribeRole.Theorem))));
}
