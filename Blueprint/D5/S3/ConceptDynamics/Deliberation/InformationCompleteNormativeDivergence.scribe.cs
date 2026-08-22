using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.D5.S3.ConceptDynamics.Deliberation.InformationCompleteNormativeDivergence;

internal sealed class InformationCompleteNormativeDivergenceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "With distinct normative values, complete information permits disagreement; "
            + "incomplete information permits consensus blind to a Boolean target.",
        H("Information-Complete Normative Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-information-permits-normative-divergence"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Deliberation/"
                        + "InformationCompleteNormativeDivergence."
                        + "complete_information_permits_normative_divergence"),
                H("Complete information permits normative divergence"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any nonempty state type and any two distinct normative values, an "
                            + "injective concept admits two normative functions that disagree at "
                            + "a state. The constant functions at the chosen values provide the "
                            + "disagreement, so informational completeness does not impose a "
                            + "unique norm.")),
                    Paragraph(Text(
                        "For every noninjective concept, two equal Boolean normative functions "
                            + "witness consensus while a Boolean target remains impossible to "
                            + "recover from the concept. Consensus here is equality of the two "
                            + "normative functions, not a claim that all possible norms agree.")),
                    Paragraph(Text(
                        "A collision in the concept fiber supplies the separating target: it "
                            + "distinguishes states that the concept identifies, and therefore "
                            + "cannot factor through any Boolean answer on the concept's "
                            + "codomain. Agreement can thus coexist with blindness to a relevant "
                            + "target."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula interfaceType = F.Id("I");
        Formula valueType = F.Id("U");
        Formula boolType = F.Id("Bool");
        Formula concept = F.Id("concept");
        Formula leftValue = F.Id("leftValue");
        Formula rightValue = F.Id("rightValue");
        Formula leftNorm = F.Id("leftNorm");
        Formula rightNorm = F.Id("rightNorm");
        Formula witness = F.Id("witness");
        Formula target = F.Id("target");
        Formula answer = F.Id("answer");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula conceptType = Call("Concept", source, interfaceType);
        Formula normativeType = Call("Concept", source, valueType);
        Formula booleanNormativeType = Call("Concept", source, boolType);

        Formula completeInformation = Seq(
            Forall, Sp, source, Comma, Sp, interfaceType, Comma, Sp, valueType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Forall, Sp, concept, Colon, Sp, conceptType, Comma, RowBreak, Grp(),
            Forall, Sp, leftValue, Comma, Sp, rightValue, Colon, Sp, valueType,
            Comma, RowBreak, Grp(),
            Open,
            Call("Nonempty", source), Sp, Land, Sp,
            leftValue, Sp, Neq, Sp, rightValue, Sp, Land, Sp,
            Call("Injective", concept),
            Close, Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, leftNorm, Comma, Sp, rightNorm, Colon, Sp, normativeType,
            Comma, RowBreak, Grp(),
            Exists, Sp, witness, Colon, Sp, source, Comma, Sp,
            Apply(leftNorm, witness), Sp, Neq, Sp, Apply(rightNorm, witness));

        Formula blindConsensus = Seq(
            Forall, Sp, source, Comma, Sp, interfaceType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Forall, Sp, concept, Colon, Sp, conceptType, Comma, RowBreak, Grp(),
            Neg, Sp, Call("Injective", concept), Sp, Rightarrow, RowBreak, Grp(),
            Exists, Sp, leftNorm, Comma, Sp, rightNorm, Comma, Sp, target,
            Colon, Sp, booleanNormativeType, Comma, RowBreak, Grp(),
            Call("NormativeConsensus", leftNorm, rightNorm), Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open,
            Exists, Sp, answer, Colon, Sp, Arrow(interfaceType, boolType), Comma, Sp,
            target, Sp, Eq, Sp, answer, Sp, Circ, Sp, concept,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Open, completeInformation, Close, Sp, Land, RowBreak, Grp(),
            Open, blindConsensus, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
