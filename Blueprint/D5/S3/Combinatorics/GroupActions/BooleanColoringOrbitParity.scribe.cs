using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GroupActions;

internal sealed class BooleanColoringOrbitParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite group acting on a finite set of sites has at least as many even "
        + "Boolean coloring orbits as odd Boolean coloring orbits.",
        H("Parity of Boolean Coloring Orbits"),
        Blocks(Describe.Lean(
            DescribeId.Create("card-odd-orbits-le-even"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/GroupActions/BooleanColoringOrbitParity.card_odd_orbits_le_even"),
            H("Odd and even coloring orbits"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite group acting on a finite set of sites. A Boolean coloring "
                    + "assigns zero or one to each site. The group acts on colorings by inverse "
                    + "relabeling. Parity is the XOR of all the site values and is invariant under "
                    + "this action. The number of orbits of colorings of parity one is at most "
                    + "the number of orbits of colorings of parity zero.")),
                Paragraph(Text(
                    "Fix an element of G. If it fixes an odd coloring, pointwise XOR with that "
                    + "coloring is an involution on its fixed colorings and reverses parity. "
                    + "The odd and even fixed-point counts are then equal. If there is no odd "
                    + "fixed coloring, the odd fixed-point count is zero. Summing these "
                    + "inequalities and applying Burnside's lemma to both parity classes "
                    + "gives the orbit inequality after cancellation of the positive group order.")),
                Paragraph(Text(
                    "This inequality is an independent prerequisite for the parity imbalance "
                    + "argument when tree contexts are restored by two choices per marked slot. "
                    + "See https://github.com/the-omega-institute/trureturing/issues/34249#issuecomment-7174384750 "
                    + "and https://github.com/the-omega-institute/trureturing/issues/34249#issuecomment-7174518467."))),
            DescribeRole.Theorem))));
}
