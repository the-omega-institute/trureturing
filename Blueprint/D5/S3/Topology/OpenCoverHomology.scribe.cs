using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OpenCoverHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/OpenCoverHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduced Mayer–Vietoris gives actual positive-degree open-cover splittings.",
        H("Positive singular homology from open covers"),
        Blocks(
            Node("inclusion", "inclusionIso", "The actual Mayer\u2013Vietoris inclusion is an isomorphism",
                "Let C be an abelian category with the required coproducts and R a coefficient object. For two open subsets U,V covering a TopCat space X, if their intersection is empty or contractible, the actual Mayer–Vietoris map from H_q(U;R) biproduct H_q(V;R) to H_q(X;R) is invertible for every q>0. Exactness at the biproduct gives injectivity and exactness at X gives surjectivity. The connecting map factors through reduced H_(q-1) of the intersection. In degree one this is reduced H_0; ordinary H_0 of a nonempty contractible intersection is not asserted to vanish. The proof directly uses TopCat.mayerVietoris_exact₂, TopCat.mayerVietoris_exact₃, TopCat.reducedMayerVietorisδ_comp_ι and the TauCeti reduced-homology vanishing and successor comparison. This is the classical open Mayer–Vietoris argument from Hatcher, Chapter 2, implemented using the existing TauCeti source port.", DescribeRole.Definition),
            Node("sum", "sumIso", "Additivity for a binary topological sum",
                "For arbitrary topological spaces X,Y and q>0, their actual singular homology biproduct maps isomorphically to H_q(X sum Y;R). The summand ranges are disjoint open subsets covering the sum; their subspaces are identified by actual homeomorphisms. The empty intersection uses the empty-space branch of inclusionIso. This is not an assumed chain-level coproduct comparison.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/hatcher2002algebraic")),
            Blocks(Paragraph(Text(prose))), role);
}
