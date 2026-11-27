using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal;

internal sealed class TameExponentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tame Exponent", H("Tame Exponent"),
        Blocks(
            Paragraph(Text("Fundamental tame characters of inertia; existence of exponents; link with local reciprocity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/TameExponent.exists_isTameExponent"),
                H("exists_isTameExponent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For A above w, T injective and Q = q_w^{f!}: every s in the inertia group of A has a tame exponent a (IsTameExponent), which can be taken coprime to Q − 1 for the chosen tame generator, and some s has exponent 1.")))))));
}
