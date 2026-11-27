using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class RationalPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Points", H("Rational Points"),
        Blocks(
            Paragraph(Text("Number field is a discrete cocompact lattice of covolume one in its adeles. Relative different and discriminant of CM fields with 5040th roots; trace, norm, real embedding. Rational points embed injectively and discretely in the adelic unitary group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/RationalPoints.exists_mixedEquiv_maximalReal"),
                H("exists_mixedEquiv_maximalReal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("There is a measure-preserving real-linear isomorphism from the Minkowski space of E⁺ to real functions on the infinite places of E, sending the image of a in E⁺ to v ↦ Re Φ_v(a), Φ the CM type.")))))));
}
