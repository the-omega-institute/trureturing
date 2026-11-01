using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class IndependenceComplexTorsionSeedSingularDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/IndependenceComplexTorsionSeedSingular.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-torsion in the actual seed singular homology.", H("Two-torsion in the actual seed singular homology"), Blocks(
            Node("edgefaceequiv", "edgeFaceEquiv", "Actual finite bases",
                "The seed has eleven vertices, thirty-two edges, and twenty-four triangles. Its exhaustive increasing enumerations give bijections to the actual faces of the corresponding cardinalities. The vertex, edge, and triangle bijections identify the free integer groups.", DescribeRole.Definition),
            Node("orderedseedshortcomplexiso", "orderedSeedShortComplexIso", "Both boundary squares",
                "The three basis bijections identify the ordered short complex with the original seed integer boundary short complex. Both differential squares use the original signed boundary maps and explicit finite deletion identities.", DescribeRole.Definition),
            Node("seedh1isosingular", "seedH1IsoSingular", "The same coordinate realization",
                "The seed short-complex homology is isomorphic to Mathlib singular H1 of the actual coordinate realization of seedComplex.toPreAbstractSimplicialComplex with coefficient object ModuleCat.of Z Z. This composes the boundary identification with the generic ordered-to-singular comparison.", DescribeRole.Definition),
            Node("singularseedclass-nonzero-killed-by-two", "singularSeedClass_nonzero_killed_by_two", "The transported class has order two",
                "The image of the original seedClass under this isomorphism is nonzero and its natural-number scalar multiple by two is zero. Injectivity transports nonvanishing and linearity transports the annihilation equation. This is a singular seed; the induced king-grid obstruction needed to answer Carnero Bravo Question 32 is a separate conclusion.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
