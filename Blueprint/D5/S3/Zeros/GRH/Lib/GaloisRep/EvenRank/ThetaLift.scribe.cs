using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.EvenRank;

internal sealed class ThetaLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Theta Lift", H("Theta Lift"),
        Blocks(
            Paragraph(Text("Nonzero theta lift to larger rank; Hecke polynomials twisted and gaining a string.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift.exists_theta_lift_heckePoly"),
                H("exists_theta_lift_heckePoly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Theta lift: for f ≠ 0 of rank n ≥ 1, weight (κ, e), s > n, b unramified of weight c ≤ e, some F ≠ 0 of weight κ' on I_{n+s} is spherical where f is; its rescaled Hecke polynomial is P·∏_{l<s}(X − θ_l(ϖ)), with θ_l given by AutChar.HasWeight.toAlgebraic.")))))));
}
