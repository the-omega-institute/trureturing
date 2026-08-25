using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class DiagonalEscapeNeedsTypeExtensionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Representation/DiagonalEscapeNeedsTypeExtension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six countermodels separate four closure notions, including degenerate carriers.",
        H("Diagonal Escape Needs Type Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("faithfulness-without-representation-surjectivity"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "state_faithfulness_not_representation_surjectivity"),
                H("Faithfulness does not equal representation surjectivity"),
                StatementSource.FromAuthor(StateRepresentationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use identity as the Boolean readout and the constant-false map as "
                            + "the representation. Identity distinguishes states, while true "
                            + "has no representing coordinate under the constant map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("descent-without-faithfulness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "effective_descent_not_state_faithfulness"),
                H("Effective descent does not equal state faithfulness"),
                StatementSource.FromAuthor(DescentFaithfulnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A constant Boolean readout identifies false and true, so it is not "
                            + "faithful. Identity dynamics preserve its sole realized fiber and "
                            + "therefore descend effectively to the realized image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("faithfulness-without-self-description"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "state_faithfulness_not_self_description_closure"),
                H("State faithfulness does not equal self-description closure"),
                StatementSource.FromAuthor(FaithfulnessSelfDescriptionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Boolean identity is injective. A surjective Boolean evaluator would, "
                            + "by Lawvere diagonalization, give Boolean negation a fixed point; "
                            + "case analysis refutes that fixed point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("descent-without-representation-surjectivity"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "effective_descent_not_representation_surjectivity"),
                H("Effective descent does not equal representation surjectivity"),
                StatementSource.FromAuthor(DescentRepresentationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Identity Boolean dynamics descend along identity readout. The separate "
                            + "constant-false representation still omits the true state, showing "
                            + "that dynamic closure does not supply representation coverage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("representation-without-self-description"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "representation_surjectivity_not_self_description_closure"),
                H("Representation surjectivity does not equal self-description closure"),
                StatementSource.FromAuthor(RepresentationSelfDescriptionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Boolean identity represents both states, but the carrier cannot encode "
                            + "all four Boolean endomaps. The formal contradiction again uses the "
                            + "fixed-point consequence of a surjective evaluator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("descent-without-self-description"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "effective_descent_not_self_description_closure"),
                H("Effective descent does not equal self-description closure"),
                StatementSource.FromAuthor(DescentSelfDescriptionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Boolean negation descends along identity readout because every identity "
                            + "fiber is preserved. This does not create an internal enumeration "
                            + "of all Boolean endomaps."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-carrier-audit"),
                DeclarationHandle.Create(DeclarationPrefix + "empty_degenerate_audit"),
                H("The empty carrier separates typed maps from self-description"),
                StatementSource.FromAuthor(EmptyAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On Empty, identity injectivity and surjectivity are vacuous and identity "
                            + "dynamics descend. Self-description fails because the unique empty "
                            + "endomap has no code in an empty code type."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-carrier-audit"),
                DeclarationHandle.Create(DeclarationPrefix + "unit_degenerate_audit"),
                H("The singleton carrier satisfies all four notions"),
                StatementSource.FromAuthor(UnitAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On Unit, identity readout and representation satisfy their map laws, "
                            + "identity dynamics descend, and the constant evaluator represents "
                            + "the unique Unit endomap. No nonemptiness premise is assumed."))),
                DescribeRole.Theorem))));

    private static Formula StateRepresentationFormula() =>
        Disp(Seq(
            Call("StateFaithfulness", F.Id("idBool")), Sp, Land, Sp,
            Neg, Sp, Call("RepresentationSurjectivity", F.Id("constFalse")), Dot));

    private static Formula DescentFaithfulnessFormula() =>
        Disp(Seq(
            Call("EffectiveDescent", F.Id("constFalse"), F.Id("idBool")),
            Sp, Land, Sp, Neg, Sp,
            Call("StateFaithfulness", F.Id("constFalse")), Dot));

    private static Formula FaithfulnessSelfDescriptionFormula() =>
        Disp(Seq(
            Call("StateFaithfulness", F.Id("idBool")), Sp, Land, Sp,
            Neg, Sp, Call("SelfDescriptionClosure", F.Id("Bool")), Dot));

    private static Formula DescentRepresentationFormula() =>
        Disp(Seq(
            Call("EffectiveDescent", F.Id("idBool"), F.Id("idBool")),
            Sp, Land, Sp, Neg, Sp,
            Call("RepresentationSurjectivity", F.Id("constFalse")), Dot));

    private static Formula RepresentationSelfDescriptionFormula() =>
        Disp(Seq(
            Call("RepresentationSurjectivity", F.Id("idBool")), Sp, Land, Sp,
            Neg, Sp, Call("SelfDescriptionClosure", F.Id("Bool")), Dot));

    private static Formula DescentSelfDescriptionFormula() =>
        Disp(Seq(
            Call("EffectiveDescent", F.Id("idBool"), F.Id("notBool")),
            Sp, Land, Sp, Neg, Sp,
            Call("SelfDescriptionClosure", F.Id("Bool")), Dot));

    private static Formula EmptyAuditFormula() =>
        Disp(Seq(
            Call("StateFaithfulness", F.Id("idEmpty")), Sp, Land, Sp,
            Call("RepresentationSurjectivity", F.Id("idEmpty")), Sp, Land, Sp,
            Call("EffectiveDescent", F.Id("idEmpty"), F.Id("idEmpty")),
            Sp, Land, Sp, Neg, Sp,
            Call("SelfDescriptionClosure", F.Id("Empty")), Dot));

    private static Formula UnitAuditFormula() =>
        Disp(Seq(
            Call("StateFaithfulness", F.Id("idUnit")), Sp, Land, Sp,
            Call("RepresentationSurjectivity", F.Id("idUnit")), Sp, Land, Sp,
            Call("EffectiveDescent", F.Id("idUnit"), F.Id("idUnit")),
            Sp, Land, Sp, Call("SelfDescriptionClosure", F.Id("Unit")), Dot));
}
