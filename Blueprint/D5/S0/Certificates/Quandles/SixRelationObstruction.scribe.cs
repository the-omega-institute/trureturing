using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Quandles;

internal sealed class SixRelationObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six relations force two elements to coincide under both strict monotonicity laws.",
        H("A six-relation obstruction in ordered idempotent magmas"),
        Blocks(Describe.Lean(DescribeId.Create("collapse"),
            DeclarationHandle.Create("D5/S0/Certificates/Quandles/SixRelationObstruction.sixRelation_forces_eq"),
            H("The strict-order cycle forces equality"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Certificates/gupta2025biorderability")),
            Blocks(Paragraph(Text("For an arbitrary LinearOrder and arbitrary idempotent binary operation strictly increasing in both arguments, d*g=e, g*e=h, f*d=g, d*a=c, a*c=h and f*c=e imply d=g. Under d<g the live proof derives d<e<g, c<d, a<d, a<c, h<c and e<h, yielding h<c<d<e<h. Applying that argument in the dual order rules out g<d. No rack, self-distributivity, inverse action, finiteness or nondegeneracy is assumed. The full presented-quandle refutation consumes this conclusion. This is an attributed implementation of the predecessor ordinary proof; no independent priority or novelty is asserted."))),
            DescribeRole.Theorem))));
}
