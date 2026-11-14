using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.StarForming;

internal sealed class SemanticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/StarForming/Semantics.";
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical finite maxima for H0 compositions", H("Canonical finite maxima for H0 compositions"),
        Blocks(Paragraph(Text("The set-valued local predicate is equivalent to the canonical non-induced two-leaf-star predicate, and set minimality is equivalent to canonical finite-set inclusion-minimality. For every finite index type I and arbitrary directed port relation R, including the empty family and same-block entries, the graph has SF two equal to 6|I| and beta two equal to 5|I|. The beta upper bound restricts any dissociation set to actual H0 fibers; a whole bipartition side attains the lower bound. No connectivity or cycle restriction is introduced.")),
            Node("forms_iff", "forms iff", "Exact declaration: theorem forms_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Forms G (↑S : Set V) ↔ IsStarForming G 2 S.", DescribeRole.Theorem),
            Node("minimal_iff", "minimal iff", "Exact declaration: theorem minimal_iff (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Amplification.Minimal G (↑S : Set V) ↔ IsMinimalStarForming G 2 S.", DescribeRole.Theorem),
            Node("sf_family", "sf family", "Exact declaration: theorem sf_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : SF (Amplification.family R) 2 = 6 * Fintype.card I.", DescribeRole.Theorem),
            Node("beta_family", "beta family", "Exact declaration: theorem beta_family {I : Type*} [Fintype I] [DecidableEq I] (R : I → I → Prop) : beta (Amplification.family R) 2 = 5 * Fintype.card I.", DescribeRole.Theorem)), []));
}
