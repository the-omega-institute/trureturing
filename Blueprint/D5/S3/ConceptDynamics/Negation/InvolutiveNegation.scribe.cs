using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class InvolutiveNegationDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Negation/InvolutiveNegation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Point negation selects from complements; involution adds reversible coherence.",
        H("Involutive Negation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("avoidance-selectors-choose-from-point-complements"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "avoidanceSelector_mem_pointComplement"),
                H("Avoidance selectors choose from point complements"),
                StatementSource.FromAuthor(AvoidanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An avoidance selector carries a chosen point for every input together "
                            + "with the proof that the chosen point differs from that input.")),
                    Paragraph(Text(
                        "Since the point complement is exactly the set of unequal points, the "
                            + "selector's avoidance field is precisely the required membership "
                            + "witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("involutive-negation-induces-an-involutive-set-action"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "imageSet_involutive"),
                H("Involutive negation induces an involutive set action"),
                StatementSource.FromAuthor(ImageSetInvolutiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The subset action sends a set through the point-negation map. Membership "
                            + "in the image can be tested by negating the candidate point once.")),
                    Paragraph(Text(
                        "Applying the image action twice negates every point twice. The structure "
                            + "field asserting pointwise involution then returns exactly the "
                            + "original subset."))),
                DescribeRole.Theorem))));

    private static Formula AvoidanceFormula()
    {
        Formula state = F.Id("X");
        Formula selector = F.Id("selector");
        Formula x = F.Id("x");

        return Disp(Seq(
            Forall, Sp, selector, Colon, Sp, Call("AvoidanceSelector", state),
            Comma, Sp,
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Call(
                "member",
                Call("choose", selector, x),
                Call("pointComplement", x)),
            Dot));
    }

    private static Formula ImageSetInvolutiveFormula()
    {
        Formula state = F.Id("X");
        Formula negation = F.Id("negation");
        Formula subset = F.Id("A");

        return Disp(Seq(
            Forall, Sp, negation, Colon, Sp,
            Call("InvolutiveNegation", state), Comma, Sp,
            Call("imageSet", negation, Call("imageSet", negation, subset)),
            Sp, Eq, Sp, subset, Dot));
    }
}
