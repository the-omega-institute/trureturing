using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class ResidualJoinLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula baselineType = F.Id("C");
        Formula definitionType = F.Id("D");
        Formula targetType = F.Id("Y");
        Formula baseline = F.Id("q");
        Formula definition = F.Id("d");
        Formula target = F.Id("T");
        Formula type = F.Id("Type");
        Formula baselineResidual = Call("defectRelation", baseline, target);
        Formula joinedResidual = Call(
            "defectRelation", Call("conceptJoin", baseline, definition), target);
        Formula definitionKernel = Call("ker", definition);
        Formula statement = Disp(Seq(
            Forall, Sp, state, Comma, Sp, baselineType, Comma, Sp,
            definitionType, Comma, Sp, targetType, Colon, Sp, type, Comma,
            RowBreak, Grp(), baseline, Colon, Sp,
            Call("Concept", state, baselineType), Comma, Sp,
            definition, Colon, Sp, Call("Concept", state, definitionType),
            Comma, Sp, target, Colon, Sp, Call("Concept", state, targetType),
            Comma, RowBreak, Grp(), joinedResidual, Sp, Eq, Sp,
            Call("intersection", baselineResidual, definitionKernel), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Joining one definition filters the target residual by that definition's kernel.",
            H("Residual Join Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("residual-join-law"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw."
                            + "residual_join_law"),
                    H("A joined definition intersects the target residual"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For arbitrary state, baseline-coordinate, definition-coordinate, "
                                + "and target types, q, d, and T are concept readouts on the "
                                + "same state space. The source notation E is represented by the "
                                + "canonical defectRelation, q join d by conceptJoin, and ker d "
                                + "by the Setoid kernel of d on state pairs.")),
                        Paragraph(Text(
                            "The accepted concept-kernel order duality confirms the component "
                                + "kernel identity when both coordinate types share a universe. "
                                + "The public law retains independent coordinate universes: "
                                + "product projections extract the two component equalities, and "
                                + "reassociation of the target-inequality clause gives exactly "
                                + "the displayed residual intersection.")),
                        Paragraph(Text(
                            "The Lean module also checks a nonempty Boolean instance: constant "
                                + "baseline and definition readouts leave false and true in the "
                                + "joined residual for the identity target. This witnesses the "
                                + "domains and shows the equality is not certified only on an "
                                + "empty residual."))),
                    DescribeRole.Theorem))));
    }
}
