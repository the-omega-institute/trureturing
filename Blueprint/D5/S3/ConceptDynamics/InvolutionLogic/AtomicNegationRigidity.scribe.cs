using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InvolutionLogic;

internal sealed class AtomicNegationRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonempty atomic-negation universe has exactly two elements.",
        H("Atomic Negation Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("atomic-negation-exists-exactly-on-bool-carriers"),
                DeclarationHandle.Create(Prefix + "nonempty_iff_equiv_bool"),
                H("Atomic negation exists exactly on a Boolean carrier"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the carrier is nonempty. An atomic negation assigns each "
                            + "point the unique point different from it.")),
                    Paragraph(Text(
                        "Choosing one anchor transports such a negation to Boolean negation "
                            + "and yields an equivalence with Bool. Conversely, any Boolean "
                            + "equivalence transports the canonical atomic negation back.")),
                    Paragraph(Text(
                        "The equivalence is conditional on the displayed Nonempty instance; "
                            + "the statement makes no assertion for an empty carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-atomic-negation-carriers-have-cardinality-two"),
                DeclarationHandle.Create(Prefix + "card_eq_two"),
                H("A finite inhabited atomic-negation carrier has two points"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let negation be an AtomicNegation structure on a finite, inhabited "
                            + "carrier. Its fields force every point other than an anchor to "
                            + "be the anchor's negation.")),
                    Paragraph(Text(
                        "The induced equivalence with Bool transports finite cardinality, so "
                            + "the carrier has exactly two elements."))),
                DescribeRole.Theorem))));

    private static Formula ExistenceFormula()
    {
        Formula carrier = F.Id("X");
        Formula conclusion = Seq(
            Call("Nonempty", Call("AtomicNegation", carrier)),
            Sp, Iff, Sp,
            Call("Nonempty", Call("Equiv", carrier, F.Id("Bool"))));

        return Disp(Seq(
            Call("Nonempty", carrier), Sp, Rightarrow, Sp,
            Open, conclusion, Close, Dot));
    }

    private static Formula CardinalityFormula()
    {
        Formula carrier = F.Id("X");
        Formula negation = F.Id("negation");
        Formula instances = Seq(
            OpenBracket, Call("Fintype", carrier), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", carrier), CloseBracket);

        return Disp(Seq(
            Forall, Sp, negation, Colon, Sp, Call("AtomicNegation", carrier),
            Comma, Sp,
            Open, instances, Close, Sp, Rightarrow, Sp,
            Call("card", carrier), Sp, Eq, Sp, D(2), Dot));
    }
}
