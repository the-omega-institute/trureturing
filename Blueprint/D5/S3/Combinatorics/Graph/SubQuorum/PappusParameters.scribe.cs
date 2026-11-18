using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubQuorum;

internal sealed class PappusParametersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SubQuorum/PappusParameters.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/omega2026starformingfamily");
    private static DocumentBlock Node(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Pappus maxima", H("Exact Pappus maxima"),
        Blocks(Paragraph(Text("The representative maximum Omega and the sub-quorum parameter psiSq of the Pappus graph are both ten. These positive certificates are outside the proof of the beta half-order refutation and have no qualifying refutation basis.")),
            Node("omega_upper_of_objective_bound", "Omega upper from all feasible pairs", "Exact declaration: theorem omega_upper_of_objective_bound (n : ℕ) (h : ∀ T M, Feasible G T M → T.card + M.card ≤ n) : Omega G ≤ n. The finite Pappus maximum is its actual consumer.", DescribeRole.Theorem),
            Node("omega_pappus", "omega pappus", "Exact declaration: theorem omega_pappus : Omega pappusGraph = 10.", DescribeRole.Theorem),
            Node("pappus_parameters", "pappus parameters", "Exact declaration: theorem pappus_parameters : beta pappusGraph 2 = 10 ∧ psiSq pappusGraph = 10 ∧ Omega pappusGraph = 10.", DescribeRole.Theorem)), []));
}
