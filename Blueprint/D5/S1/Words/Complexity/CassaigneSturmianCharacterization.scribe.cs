using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class CassaigneSturmianCharacterizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/cassaigne2008extremal");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Uniform replication and golden-word asymptotic invariants.", H("CassaigneSturmianCharacterization"), Blocks(
            Describe.Lean(DescribeId.Create("cassaigne-cassaignesturmiancharacterization-claim"), DeclarationHandle.Create("D5/S1/Words/Complexity/CassaigneSturmianCharacterization.claim"), H("claim"), StatementSource.FromAuthor(Disp(Seq(Q("claim"), Eq, Parenthesized(ClaimBody())))), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Printed p. 707, Open problem 2: “Open problem 2. How can this equality be explained? Does it characterize Sturmian words? (Compare, for instance, with the Prouhet-Thue-Morse word which has ind*(t) = 2 and ρ*(t) = 10, see Prop. 6.1.)” The alphabet is Bool with true representing a; natural indices start at zero. The implication ranges over every infinite binary word."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cassaigne-cassaignesturmiancharacterization-result"), DeclarationHandle.Create("D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result"), H("result"), StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Replicating each letter of the golden word twice gives equal finite asymptotic invariants, both ENNReal.ofReal (2 + Real.goldenRatio). It contains both constant binary bigrams, which the irrational mechanical codings cannot contain together. The equality therefore fails to imply the stated mechanical representation. The argument treats every replication factor at least two and does not classify all equality cases."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("cassaigne-sturmian"), ResolutionKind.Refuted)))));
    private static Formula ClaimBody() => Seq(Forall, Sp, Q("u"), Sp, Colon, Sp, Q("Nat"), Sp, To, Sp, Q("Bool"), Sp, Comma, Sp, Q("indStar"), Sp, Q("u"), Sp, Eq, Sp, Q("rhoStar"), Sp, Q("u"), Sp, To, Sp, Q("IsSturmian"), Sp, Q("u"));
    private static Formula Q(string name) => Seq(Operatorname, Grp(Seq([.. name.Split('.').SelectMany((part, index) => index == 0 ? new Formula[] { F.Id(part) } : new Formula[] { Dot, part is "1" ? D(1) : F.Id(part) })])));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
