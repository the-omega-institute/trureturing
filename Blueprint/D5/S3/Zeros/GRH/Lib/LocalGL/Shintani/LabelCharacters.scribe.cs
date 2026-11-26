using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Shintani;

internal sealed class LabelCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label Characters", H("Label Characters"),
        Blocks(
            Paragraph(Text("Shintani norm via IsRootChoice: descent keeps inner products, commutes with induction; extension. Frobenius reciprocity for parabolic induction from several diagonal blocks. Shintani lifts for GL_n: definition, stability under parabolic induction and pointwise operations. Torus-induced character lifts to the semidirect product; Brauer lift has a virtual lift. Green's characters with squarefree labels are orthonormal irreducible characters of GL_r(F_q).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Shintani/LabelCharacters.lift_labelChar_self"),
                H("lift_labelChar_self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For T injective and c a label, the class function Ξ_c, the product of the τ_P over the monic irreducible factors P of c, is in every dimension a combination of characters with natural number coefficients.")))))));
}
