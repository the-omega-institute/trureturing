using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup;

internal sealed class RigidFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigid Fibres", H("Rigid Fibres"),
        Blocks(
            Paragraph(Text("Theta coordinates span the sections on fibres of a modelled abelian scheme.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/RigidFibres.isRigid_pullback"),
                H("isRigid_pullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Rigidity of geometric fibres: if an object y over a valuation ring O with fraction field ℂ is modelled on a complex torus, every pull-back of y along a homomorphism from O to an algebraically closed field satisfies ThetaObject.IsRigid.")))))));
}
