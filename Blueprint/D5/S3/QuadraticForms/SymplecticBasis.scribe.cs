using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SymplecticBasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-dimensional nondegenerate alternating form has a symplectic basis, including the zero space.",
        H("Finite-Dimensional Symplectic Basis"),
        Blocks(Describe.Lean(
            DescribeId.Create("symplectic-basis-existence"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/SymplecticBasis.exists_isSymplecticBasis"),
            H("Attributed Darboux basis construction"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("K"), Comma, Sp, F.Id("V"), Comma, Sp, F.Id("B"), Comma, Sp,
                Call("Field", F.Id("K")), Sp, Land, Sp,
                Call("FiniteDimensional", F.Id("K"), F.Id("V")), Sp, Land, Sp,
                Call("IsAlt", F.Id("B")), Sp, Land, Sp,
                Call("Nondegenerate", F.Id("B")), Sp, Rightarrow, Sp,
                Exists, Sp, F.Id("n"), Comma, Sp, F.Id("e"), Comma, Sp,
                Call("IsSymplecticBasis", F.Id("B"), F.Id("e"))))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/blore2026symplecticbasis")),
            Blocks(
                Paragraph(Text("Over any field K, on any finite-dimensional additive K-module V, every nondegenerate alternating bilinear form B admits a basis indexed by Fin n plus Fin n for some natural n. The two halves pair internally to zero and across halves by the Kronecker delta, with B(p_i,q_i)=+1. Dimension zero is included.")),
                Paragraph(Text("The proof is an attributed bounded port of Zayn Blore's CsdLean4 construction at immutable revision 39182b9e91a2791f5acb5ceaa2612ed71da921b5. It extracts a symplectic plane, proves nondegeneracy on its orthogonal complement, and recurses by finite dimension. The auxiliary induction and index equivalence stay inside the existence proof.")),
                Paragraph(Text("For predictive symplectic completion, this supplies bases for im L and ker O when the alternating form restricted to each space is nondegenerate. It does not establish those nondegeneracy hypotheses, mixed-energy vanishing or positive Williamson blocks. Its positive cross-pairing convention is opposite to Mathlib's Matrix.J."))),
            DescribeRole.Theorem))));
}
