using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class RetirementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/Retirement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit edge-flow ledger verifies starts, all interior transitions, and both terminal geometries without adding a cycle condition.",
        H("Frontier Retirement and Boundary Flow"),
        Blocks(
            Describe.Lean(DescribeId.Create("flow-ledger"),
                DeclarationHandle.Create(Prefix + "boundaryFlow"), H("Residual semitone boundary flow"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Flow is an integer function on ZMod n. An edge contributes +1 at its source and -1 at its target; a configuration combines the five-state frontier with the running +1 charge. The final boundaryFlow is supported at the two semitone residues, so zero charge is exactly the remaining balance condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("class-two-starts"),
                DeclarationHandle.Create(Prefix + "start_classification"),
                H("The four admissible starts split by sign"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The only allowed class-two forms split into positive II/IV and negative III/V starts. Their distinct labels, initial states, and charges agree with PathData's two start tables. This establishes the beginning of the inverse classification."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("interior-flow-step"),
                DeclarationHandle.Create(Prefix + "transition_flow"),
                H("One labelled step preserves the flow invariant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For each indexed transition, adding its low and high edges transforms the current frontier flow into the next configuration and adds precisely its stored charge. All twelve labels in each sector are checked; the shared topology alone would not prove this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-antipodal-boundary"),
                DeclarationHandle.Create(Prefix + "even_terminal_flow"),
                H("The even antipodal pair retires the frontier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "At n=6r the last two classes form an antipodal pair. The six boundary positions are proved distinct for r>=1, and the sector-specific terminal labels leave only the recorded semitone charge. The odd singleton has its own theorem and cannot be inferred from this pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-singleton-boundary"),
                DeclarationHandle.Create(Prefix + "odd_terminal_flow"),
                H("The odd singleton retires the frontier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "At n=6r+3 one central class remains. Its single label and charge are checked in both sectors against the final boundary flow; using the even antipodal table here would change the counted object."))),
                DescribeRole.Theorem)), []));
}
