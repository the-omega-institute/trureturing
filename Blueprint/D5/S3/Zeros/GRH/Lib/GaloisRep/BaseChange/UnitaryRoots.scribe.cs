using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange;

internal sealed class UnitaryRootsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary Roots", H("Unitary Roots"),
        Blocks(
            Paragraph(Text("Hasse principle for norms in one CM field via reciprocity and Hasse's norm theorem. Adelically split unitary cocycles split rationally (Landherr); normal matrices are semisimple. Polynomial roots inverting the norm map; products of local matching pairs.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/UnitaryRoots.hasse_principle_coboundary"),
                H("hasse_principle_coboundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Hasse principle for cocycles: for E stably unramified, E'/E Galois of prime degree, σ ≠ 1, a rational point s of the standard definite U(n) over E' with twisted norm 1 that equals uσ(u)⁻¹ over the finite adeles equals gσ(g)⁻¹ with g rational.")))))));
}
