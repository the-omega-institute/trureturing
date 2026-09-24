using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DegeneracyGraphMonomialBasisDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/DegeneracyGraphMonomialBasis";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/kempramgoolam2026degeneracy");
    private static DocumentBlock.Describe Declaration(int number, string name) =>
        Describe.Lean(DescribeId.Create($"declaration-{number:00}"), DeclarationHandle.Create($"{Module}.{name}"), H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("This public declaration is the actual arbitrary-algebra source bridge. It is projected from Lean without replacing the source monomial, projector, or coefficient orientation by a postulated evaluation equivalence."))), name == "source_monomial_basis_and_expansions" ? DescribeRole.Theorem : DescribeRole.Definition, name == "source_monomial_basis_and_expansions" ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("kemp-ramgoolam-degeneracy-graph-determinant-and-monomial-basis"), ResolutionKind.Proved) : null);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual source monomials form a basis in every commutative complex algebra with complete orthogonal leaf projectors.",
        H("Degeneracy Graph Monomial Basis"),
        Blocks(
            Paragraph(Text("The basis owner contains the complete public inventory: sourceNodeProjector sums the actual descendant leaf projectors, sourceGenerator uses the literal node labels, and sourceMonomial is the literal generator-product monomial. The final theorem constructs P : Basis (Bottom T) Complex A to B : Basis (Columns T) Complex A, proves B m = sourceMonomial T P m, gives the forward RawM expansion (2.29), and gives the inverse projector expansion (2.30) with coefficient (SourceSquare T)^-1 ((bottomColumnEquiv T).symm m) b. The algebra is arbitrary [CommRing A] [Algebra Complex A]; no semisimplicity or evaluation-isomorphism assumption is introduced.")),
            Paragraph(Text("This is the exact source resolution of the monomial-basis clause (3.6), joined to the determinant bridge through the accepted factorization theorem.")),
            Declaration(1, "sourceNodeProjector"), Declaration(2, "sourceGenerator"), Declaration(3, "sourceMonomial"), Declaration(4, "source_monomial_basis_and_expansions"))));
}
