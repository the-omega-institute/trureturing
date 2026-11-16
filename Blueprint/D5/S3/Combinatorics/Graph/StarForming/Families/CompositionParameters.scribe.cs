using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming.Families;

internal sealed class CompositionParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Families/CompositionParameters.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical finite maxima for H0 compositions", H("Canonical finite maxima for H0 compositions"),
        Blocks(Paragraph(Text("For every finite index type I and arbitrary directed port relation R, including the empty family and same-block entries, the original H0 family has SF two equal to 6|I| and beta two equal to 5|I|. Restriction to actual H0 fibers gives the beta upper bound; a whole bipartition side attains the lower bound. No connectivity or cycle restriction is introduced.")),
            Node("sf_family", "sf family", "Exact declaration: theorem sf_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : SF (Amplification.family R) 2 = 6 * Fintype.card I.", DescribeRole.Theorem),
            Node("beta_family", "beta family", "Exact declaration: theorem beta_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : beta (Amplification.family R) 2 = 5 * Fintype.card I.", DescribeRole.Theorem)), []));
}
