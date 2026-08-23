using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class CredentialMultiplicityCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Credential transcripts cannot recover person vote counts without owner multiplicity.",
        H("Credential Multiplicity Countermodel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("credential-transcript-cannot-recover-person-vote-count"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/CredentialMultiplicityCountermodel."
                        + "credential_transcript_cannot_recover_person_vote_count"),
                H("Credential transcripts do not determine person vote counts"),
                StatementSource.FromAuthor(CountermodelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A credential world contains an owner map and Boolean credential votes. "
                            + "Its public transcript exposes only the votes. Credential vote count "
                            + "counts affirmative credentials, while person vote count takes the "
                            + "finite image of their owners before counting.")),
                    Paragraph(Text(
                        "The common-owner world assigns both affirmative credentials to one person. "
                            + "The distinct-owner world uses the identity owner map. Their public "
                            + "transcripts and credential counts agree, but their person counts are "
                            + "one and two.")),
                    Paragraph(Text(
                        "Any recovery function on public transcripts must return the same value on "
                            + "these two worlds, contradicting their distinct person counts. The "
                            + "display also records the failed and satisfied injectivity conditions "
                            + "on the two owner maps."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CountermodelFormula()
    {
        Formula common = F.Id("commonOwnerWorld");
        Formula distinct = F.Id("distinctOwnerWorld");
        Formula transcriptCommon = Call("publicTranscript", common);
        Formula transcriptDistinct = Call("publicTranscript", distinct);
        Formula ownerCommon = Call("owner", common);
        Formula ownerDistinct = Call("owner", distinct);
        Formula credentialsCommon = Call("credentialVoteCount", common);
        Formula credentialsDistinct = Call("credentialVoteCount", distinct);
        Formula personsCommon = Call("personVoteCount", common);
        Formula personsDistinct = Call("personVoteCount", distinct);
        Formula finTwo = Call("Fin", D(2));
        Formula transcriptType = Arrow(finTwo, F.Id("Bool"));
        Formula recoverType = Arrow(Seq(Open, transcriptType, Close), F.Id("Nat"));
        Formula factorization = Seq(
            F.Id("personVoteCount"), Sp, Eq, Sp, F.Id("recover"), Sp, Circ, Sp,
            F.Id("publicTranscript"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            transcriptCommon, Sp, Eq, Sp, transcriptDistinct, Sp, Land, RowBreak, Grp(),
            Apply(ownerCommon, D(0)), Sp, Eq, Sp, Apply(ownerCommon, D(1)), Sp, Land,
            RowBreak, Grp(),
            Apply(ownerDistinct, D(0)), Sp, Neq, Sp, Apply(ownerDistinct, D(1)), Sp, Land,
            RowBreak, Grp(),
            credentialsCommon, Sp, Eq, Sp, D(2), Sp, Land, Sp,
            credentialsDistinct, Sp, Eq, Sp, D(2), Sp, Land, RowBreak, Grp(),
            personsCommon, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            personsDistinct, Sp, Eq, Sp, D(2), Sp, Land, RowBreak, Grp(),
            Neg, Sp, Open, Exists, Sp, F.Id("recover"), Colon, Sp, recoverType, Comma, Sp,
            factorization, Close, Sp, Land, RowBreak, Grp(),
            Neg, Sp, Call("Injective", ownerCommon), Sp, Land, Sp,
            Call("Injective", ownerDistinct), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
