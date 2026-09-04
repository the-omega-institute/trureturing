using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class ExistenceNotionSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ExistenceNotionSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formability, proof, construction, model existence, and realization are distinct predicates.",
        H("Existence-Notion Separation"),
        Blocks(
            Node(
                "has-model",
                "HasModel",
                "Model existence",
                "A model exists exactly when the externally supplied model predicate has a witness.",
                DescribeRole.Definition),
            Node(
                "realized",
                "Realized",
                "Realization",
                "Realization is an externally supplied relation between a model and a constructed object.",
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mathematical-existence-notions-separate"),
                DeclarationHandle.Create(Prefix + "mathematical_existence_notions_separate"),
                H("Mathematical existence notions separate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "False is a formed proposition without a proof, and Empty is a formed "
                            + "type without a construction. Every explicit construction nevertheless "
                            + "supplies a Nonempty witness.")),
                    Paragraph(Text(
                        "External model and realization predicates each admit explicit positive "
                            + "and negative examples. The theorem therefore compares the formal "
                            + "notions without elevating one philosophical doctrine into a kernel fact."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula() => Disp(Seq(
        Begin, Grp(F.Id("aligned")),
        Amp, Open, Exists, Sp, F.Id("P"), Colon, Sp, F.Id("Prop"), Comma, Sp,
        Neg, Sp, F.Id("P"), Close, Sp, Land, RowBreak,
        Amp, Open, Exists, Sp, F.Id("X"), Colon, Sp, F.Id("Type"), Comma, Sp,
        F.Id("IsEmpty"), Open, F.Id("X"), Close, Close, Sp, Land, RowBreak,
        Amp, Open, Forall, Sp, F.Id("X"), Colon, Sp, F.Id("Type"), Comma, Sp,
        new Formula.TypeArrow(
            Seq(F.Id("X")),
            Seq(F.Id("Nonempty"), Open, F.Id("X"), Close)),
        Close, Sp, Land, RowBreak,
        Amp, Open, Exists, Sp, F.Id("M"), Colon, Sp, F.Id("Type"), Comma, Sp,
        F.Id("q"), Colon, Sp, ModelPredicateType(), Comma, Sp,
        F.Id("HasModel"), Open, F.Id("q"), Close, Close, Sp, Land, RowBreak,
        Amp, Open, Exists, Sp, F.Id("M"), Colon, Sp, F.Id("Type"), Comma, Sp,
        F.Id("q"), Colon, Sp, ModelPredicateType(), Comma, Sp,
        Neg, Sp, F.Id("HasModel"), Open, F.Id("q"), Close, Close, Sp, Land, RowBreak,
        Amp, NegativeRealizationFormula(), Sp, Land, RowBreak,
        Amp, PositiveRealizationFormula(), Dot,
        End, Grp(F.Id("aligned"))));

    private static Formula ModelPredicateType() => new Formula.TypeArrow(
        Seq(F.Id("M")), Seq(F.Id("Prop")));

    private static Formula RealizationRelationType() => new Formula.TypeArrow(
        Seq(F.Id("M")),
        new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Prop"))));

    private static Formula NegativeRealizationFormula() => Seq(
        Open, Exists, Sp, F.Id("M"), Comma, Sp, F.Id("X"), Colon, Sp, F.Id("Type"), Comma, Sp,
        F.Id("m"), Colon, Sp, F.Id("M"), Comma, Sp,
        F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
        F.Id("R"), Colon, Sp, RealizationRelationType(), Comma, Sp,
        Neg, Sp, F.Id("Realized"), Open, F.Id("R"), Comma, Sp,
        F.Id("m"), Comma, Sp, F.Id("x"), Close, Close);

    private static Formula PositiveRealizationFormula() => Seq(
        Open, Exists, Sp, F.Id("M"), Comma, Sp, F.Id("X"), Colon, Sp, F.Id("Type"), Comma, Sp,
        F.Id("m"), Colon, Sp, F.Id("M"), Comma, Sp,
        F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
        F.Id("R"), Colon, Sp, RealizationRelationType(), Comma, Sp,
        F.Id("Realized"), Open, F.Id("R"), Comma, Sp,
        F.Id("m"), Comma, Sp, F.Id("x"), Close, Close);
}
