using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class AssignmentMomentReindexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/AssignmentMomentReindex.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite assignment moments under enumeration.",
        H("Assignment moment reindexing"),
        Blocks(
            Paragraph(Text("Let D and T be finite types, A a commutative real algebra, ell a real linear functional on A, and Y a family indexed by D. Enumerating T preserves both the scalar weight product and the algebra product in each injective assignment moment.")),
            Entry("assignment-moment-reindex", "assignment_moment_reindex", "Distinct-index moment under any enumeration",
                "For any finite type T and equivalence e from T to Fin n, the injective-assignment sum of the product of scalar weights "
                + "times ell of the product of Y factors equals the ordered distinct-index moment of the weights composed with e.inverse. "
                + "Both scalar and algebra products are unchanged by the enumeration.", DescribeRole.Theorem),
            Entry("retained-assignment-reindex", "retained_assignment_reindex", "Enumeration of retained assignments",
                "For every finite subset S of a label type B and scalar weights w indexed by B, the sum over injective maps x from S to D "
                + "of the product of w(t,x(t)) over t in S times ell of the product of Y(x(t)) over t in S equals the ordered distinct-index moment "
                + "of the weights w((equivFin(S)).inverse(i)), indexed by Fin(card(S)). The equality is finite reindexing by equivFin.", DescribeRole.Theorem))));
}
