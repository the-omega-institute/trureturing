using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class CassaigneGoldenRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/cassaigne2008extremal");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Uniform replication and golden-word asymptotic invariants.", H("CassaigneGoldenRecurrence"), Blocks(
            Describe.Lean(DescribeId.Create("cassaigne-cassaignegoldenrecurrence-golden-rhostar-eq-sharp"), DeclarationHandle.Create("D5/S1/Words/ReturnWords/CassaigneGoldenRecurrence.golden_rhoStar_eq_sharp"), H("golden rhoStar eq sharp"), StatementSource.FromAuthor(Disp(Seq(Q("rhoStar"), Sp, Q("goldenWord"), Sp, Eq, Sp, Q("ENNReal.ofReal"), Sp, Parenthesized(Seq(D(2), Sp, Plus, Sp, Q("Real.goldenRatio")))))), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains."))), DescribeRole.Theorem))));

    private static Formula Q(string name) => Seq(Operatorname, Grp(Seq([.. name.Split('.').SelectMany((part, index) => index == 0 ? new Formula[] { F.Id(part) } : new Formula[] { Dot, part is "1" ? D(1) : F.Id(part) })])));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
