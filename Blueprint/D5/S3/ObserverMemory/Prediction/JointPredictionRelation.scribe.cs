using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class JointPredictionRelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A joint observation identifies exactly the pairs identified by every component observation.",
        H("Joint Prediction Relation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-prediction-relation-is-the-component-intersection"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Prediction/JointPredictionRelation.joint_prediction_relation"),
                H("The joint prediction relation is the component intersection"),
                StatementSource.FromAuthor(RelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q_i be an arbitrary indexed family of observations on one carrier. "
                        + "The joint observation sends a point to the dependent function of all "
                        + "its component readings. Two points have the same joint reading exactly "
                        + "when every component gives them the same reading. Thus the relation "
                        + "induced by the joint observation is the indexed intersection of the "
                        + "component relations.")),
                    Paragraph(Text(
                        "The pinned library was searched before proving. Exact declaration hits "
                        + "were funext_iff for equality of dependent functions and Set.mem_iInter "
                        + "for membership in an indexed intersection. Searches for "
                        + "predictionRelation, joint_prediction_relation, and a packaged joint "
                        + "observation kernel theorem returned no hit. The proof composes the two "
                        + "library declarations after set extensionality.")),
                    Paragraph(Text(
                        "The statement is fully general in the carrier, index type, and the "
                        + "possibly index-dependent reading types. It asserts only equality of "
                        + "the induced relations; it does not claim finiteness, independence, a "
                        + "cardinality formula, or a metric fusion law. The source claim contains "
                        + "no numerical certificate."))),
                DescribeRole.Theorem))));

    private static Formula Relation(Formula observation, Formula x, Formula y) => Seq(
        F.Id("R"), Underscore, Grp(observation), Open, x, Comma, Sp, y, Close);

    private static Formula RelationFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula joint = Seq(F.Id("q"), Underscore, Grp(F.Id("I")));
        Formula component = Seq(F.Id("q"), Underscore, Grp(i));
        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, y, Comma, Esc,
            Relation(joint, x, y), Sp, Iff, Sp,
            Open, Forall, Sp, i, Comma, Esc,
            Relation(component, x, y), Close, Dot));
    }
}
