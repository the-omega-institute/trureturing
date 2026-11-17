using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixDimensionalProfilesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/SixDimensionalProfiles.";
    private static DocumentBlock Item(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")),
        Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All full exact profiles of the actual nonclique graph.", H("All full exact profiles of the actual nonclique graph"),
        Blocks(
            Item("represented-profile", "represented_profile", "Recover every full K/P pair",
                "Every represented actual six-coordinate submodule has exactly its specified full kernel and projection, for every quotient-valued placement map including all degenerate fibers.", DescribeRole.Theorem),
            Item("profile", "profile", "The exact full profile of every actual vertex",
                "The map retains K and the entire nonzero P for every actual submodule outside T. The preceding owner proves equivalence with the source dimension/K/H profile.", DescribeRole.Definition),
            Item("profile-surjective", "profile_surjective", "Every full pair is realized",
                "The zero placement map realizes every possible kernel and nonzero projection. Thus the profile count concerns every actual nonclique submodule and assumes no sampled profile list.", DescribeRole.Theorem),
            Item("realized-equiv", "realizedEquiv", "The complete actual image",
                "A proved bijection identifies profiles actually realized by the original full nonclique domain with all full K/P pairs.", DescribeRole.Definition),
            Item("result", "result", "Exactly240 actual exact profiles",
                "The full three-dimensional submodule lattice has16 elements, and its nonzero lattice has15. Every pair is realized, yielding240 exact source profiles. This does not imply the separate fixed-certificate139 multi-color statistic, which remains a finite-data obligation.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/SixDimensionalLiftGeometry"))]));
}
