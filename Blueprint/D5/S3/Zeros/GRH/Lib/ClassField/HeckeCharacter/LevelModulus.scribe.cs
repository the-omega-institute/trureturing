using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter;

internal sealed class LevelModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level Modulus", H("Level Modulus"),
        Blocks(
            Paragraph(Text("Surjective reduction of the level group; tame characters modulo a modulus. Polarisation of determinant powers through the Fischer pairing, from unitary to all matrices. The modulus M^c Q built from the chosen places and its support.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LevelModulus.matrix_ext_modulusResidue"),
                H("matrix_ext_modulusResidue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Chinese remainder theorem: if the ideal of 𝔪 is the product of distinct primes w_i, two matrices over O_E/𝔪 are equal if and only if their reductions at every w_i are equal.")))))));
}
