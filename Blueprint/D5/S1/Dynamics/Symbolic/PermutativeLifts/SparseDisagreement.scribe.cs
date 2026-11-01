using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class SparseDisagreementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite phase control of disagreement in equal-height marked tilings.",
        H("Sparse disagreement and finite windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("bad-phases"), DeclarationHandle.Create(Owner + "badPhases"),
                H("Exceptional phases"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive height L, let D be a finite set of residues modulo L. A phase is exceptional for the signed window starting at t with length r when adding one of t, t+1, ..., t+r-1 lands in D. The exceptional set is the union of the corresponding r translates of D."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("phase-count"), DeclarationHandle.Create(Owner + "badPhases_card_le"),
                H("Exceptional-phase count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The number of exceptional phases is at most r times the size of D. The finite-union bound counts at most one copy of D per window coordinate, allowing overlap between translates and including r=0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("offset-phase"), DeclarationHandle.Create(Owner + "offset_cast"),
                H("Physical cyclic phase law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Casting the two-sided physical offset law to the finite cyclic group turns the integer remainder formula into addition of the translated coordinate. This bridge is shared by the finite-window argument and the actual invariant-measure phase factor."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("same-phase-window"), DeclarationHandle.Create(Owner + "same_phase_window"),
                H("Agreement across all seams"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take two actual marked tilings by two Boolean words of the same positive length. Their physical offsets evolve by the cyclic phase law from EqualLengthTiling. If their offsets at zero agree and this initial phase avoids the translates of the words' differing columns, the two readouts agree at every coordinate of the window. The conclusion covers negative starting coordinates and windows crossing any number of tile boundaries; it assumes neither a common tile type nor a choice of a point in each phase fibre."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("column-count"), DeclarationHandle.Create(Owner + "wordDisagreements_card"),
                H("Literal columns and list mismatch"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The differing-column set consists precisely of residues whose aligned letters differ. Its cardinality equals the list mismatch count used by BalancedWords. This interface transports the exact combinatorial recurrence to the physical phase coordinates of actual tilings."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-bound"), DeclarationHandle.Create(Owner + "balanced_badPhases_card_scaled"),
                H("Balanced exceptional-phase estimate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual equal-height balanced factorial words at level n, the existing identity 3^n d(n)=h(n) gives 3^n times the number of exceptional phases at most r h(n). The integral estimate avoids division and rounding. It supplies the finite phase input for a separate invariant-measure cylinder argument; no existence or uniqueness of invariant measures is asserted in this module."))), DescribeRole.Theorem))));
}
