using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ScopedOrientationSpecDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ScopedOrientationSpec.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exogenous orientation specification induces a preorder on its admissible scope.",
        H("Scoped Orientation Specification"),
        Blocks(
            Node(
                "orientation-spec",
                "OrientationSpec",
                "Orientation specification",
                "The specification stores an external relation, provenance, version, scope, "
                    + "and relation laws whose hypotheses explicitly consume eligibility and scope.",
                DescribeRole.Definition),
            Node(
                "admissible-target",
                "AdmissibleTarget",
                "Admissible scoped target",
                "The operator domain is the subtype of targets that are both eligible for the "
                    + "fixed goal and members of the specification scope.",
                DescribeRole.Definition),
            Node(
                "orient",
                "orient",
                "Orientation projection",
                "The orientation operator projects the external relation to two admissible "
                    + "scoped targets; an out-of-scope target cannot be passed to this operator.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("scoped-orientation-is-preorder"),
                DeclarationHandle.Create(Prefix + "scoped_orientation_is_preorder"),
                H("Scoped orientation is a preorder"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each admissible target carries the eligibility and scope witnesses "
                            + "required by the specification's reflexivity proof.")),
                    Paragraph(Text(
                        "Three such targets similarly supply every premise of the external "
                            + "transitivity proof. The specification therefore induces a preorder "
                            + "without manufacturing the goal or any normative source."))),
                DescribeRole.Theorem),
            Node(
                "scoped-preorder",
                "scopedPreorder",
                "Scoped preorder structure",
                "The proven relation laws are packaged as a Preorder on the admissible subtype.",
                DescribeRole.Definition))));

    private static DocumentBlock.Describe Node(
        string id,
        string declaration,
        string title,
        string paragraph,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            role);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula eligibleType = new Formula.TypeArrow(
            Seq(F.Id("Target")),
            new Formula.TypeArrow(Seq(F.Id("Goal")), Seq(F.Id("Prop"))));
        Formula specType = Call(
            "OrientationSpec",
            F.Id("Goal"),
            F.Id("Target"),
            F.Id("Source"),
            F.Id("Version"),
            F.Id("G"),
            F.Id("Eligible"));
        Formula spec = F.Id("spec");
        Formula domain = Call("AdmissibleTarget", spec);
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula third = F.Id("c");
        Formula reflexive = Seq(
            Forall, Sp, first, Colon, Sp, domain, Comma, Sp,
            Call("orient", spec, first, first));
        Formula transitive = Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp, third,
            Colon, Sp, domain, Comma, Sp,
            Call("orient", spec, first, second), Sp, Rightarrow, Sp,
            Call("orient", spec, second, third), Sp, Rightarrow, Sp,
            Call("orient", spec, first, third));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, F.Id("Goal"), Comma, Sp, F.Id("Target"), Comma, Sp,
            F.Id("Source"), Comma, Sp, F.Id("Version"), Colon, Sp, type, Comma,
            RowBreak, Grp(),
            F.Id("G"), Colon, Sp, F.Id("Goal"), Comma, Sp,
            F.Id("Eligible"), Colon, Sp, eligibleType, Comma, RowBreak, Grp(),
            spec, Colon, Sp, specType, Comma, RowBreak, Grp(),
            Open, reflexive, Close, Sp, Land, RowBreak, Grp(),
            Open, transitive, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
