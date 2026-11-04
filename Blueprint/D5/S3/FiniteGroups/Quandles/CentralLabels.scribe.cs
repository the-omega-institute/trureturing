using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Quandles;

internal sealed class CentralLabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Quandles/CentralLabels.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/ta2025goodinvolutions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-group good involutions are exactly compatible class-invariant central labels.",
        H("CentralLabels"),
        Blocks(
            Describe.Lean(DescribeId.Create("ta116-isgood"),
                DeclarationHandle.Create(Prefix + "IsGood"), H("The original good-map identities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The involution commutes with every conjugation, and conjugation by its value at x is conjugation by the inverse of x. This uses the source convention s_x(y)=xyx^-1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-good"),
                DeclarationHandle.Create(Prefix + "Good"), H("Good maps as functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The subtype counts actual functions and introduces no quotient by isomorphism."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-label"),
                DeclarationHandle.Create(Prefix + "Label"), H("Central label functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A label assigns a central element to every group element, is constant on conjugacy classes, and is unchanged after its own twisted inversion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-goodlabelequiv"),
                DeclarationHandle.Create(Prefix + "goodLabelEquiv"), H("Complete central-label classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For an arbitrary group, the label of a good map rho is z(x)=rho(x)x. Conversely rho(x)=z(x)x^-1. Centrality and class invariance give the two conjugation identities, and the label compatibility is exactly rho squared equals identity. This is the whole-group specialization of Ta Theorem 6.7; it is attributed to that source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ta116-wholegoodequiv"),
                DeclarationHandle.Create(Prefix + "wholeGoodEquiv"), H("The existing whole-carrier interface"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Transport along the evident equivalence between G and the subtype of Finset.univ identifies the pointwise whole-group definition with the repository Good definition, including both inverse identities."))), DescribeRole.Definition))));
}
