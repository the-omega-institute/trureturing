using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Revision;

internal sealed class EvolutionEvidencePullbackIdentityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Revision/EvolutionEvidencePullbackIdentity."
            + "evolution_evidence_pullback_identity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct-image evolution after pulled-back evidence equals future conditioning.",
        H("Evolution Evidence Pullback Identity"),
        Blocks(Describe.Lean(
            DescribeId.Create("evolution-evidence-pullback-identity"),
            DeclarationHandle.Create(Declaration),
            H("Evolution after evidence pullback is future conditioning"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A current state is retained exactly when its future image satisfies the "
                        + "future evidence. Taking the direct image therefore yields precisely "
                        + "the evolved admitted states intersected with that evidence.")),
                Paragraph(Text(
                    "The statement is the pinned Mathlib direct-image/intersection/preimage "
                        + "identity, applied without injectivity or surjectivity assumptions."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula current = F.Id("X");
        Formula future = F.Id("Y");
        Formula evolution = F.Id("F");
        Formula admitted = F.Id("A");
        Formula evidence = F.Id("Q");
        Formula type = F.Id("Type");

        Formula pulledBack = Call("preimage", evolution, evidence);
        Formula restricted = Call("intersection", admitted, pulledBack);
        Formula left = Call("image", evolution, restricted);
        Formula right = Call(
            "intersection",
            Call("image", evolution, admitted),
            evidence);

        return Disp(Seq(
            Forall, Sp, current, Comma, Sp, future, Colon, Sp, type, Comma, Sp,
            evolution, Colon, Sp, current, Sp, To, Sp, future, Comma, Sp,
            admitted, Colon, Sp, Call("Set", current), Comma, Sp,
            evidence, Colon, Sp, Call("Set", future), Comma, Sp,
            left, Sp, Eq, Sp, right, Dot));
    }
}
