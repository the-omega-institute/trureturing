using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA365771TwoDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/hanna2023a365771");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's second congruence modulo five.",
        H("Hanna's second congruence modulo five"),
        Blocks(
            Paragraph(Text("The natural-number sequence a and the predicate InA033042 are those of "
                + "HannaA365771. InA033042 includes zero and means that every base-five digit is "
                + "at most one. Division and subtraction use natural arithmetic. OEIS entries have "
                + "no page numbers; the source is A365771 revision 23, Comments, and A033042, Name.")),
            Describe.Lean(DescribeId.Create("hanna365771-two-claim"),
                DeclarationHandle.Create("D5/S1/Recurrence/Residue/HannaA365771Two.claim"),
                H("Hanna's second conjecture"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"),
                    FormulaLogicOperator.Iff, P(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("(2) a(5*A033042(n) + 1) == 2 (mod 5) for n > 0,"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna365771-two-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Residue/HannaA365771Two.result"),
                H("Hanna's second congruence"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The digits of 5*m+1 are one followed by the digits of m. The digit step therefore preserves membership in A033042, and the positive-index residue classification gives residue two."))), DescribeRole.Theorem))));

    private static Formula ClaimBody() => All("m", Imp(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
        Imp(Pred(F.Id("m")), Equal(new Formula.Modulo(P(A(Add(Multiply(D(5), F.Id("m")), D(1)))), D(5)), D(2)))));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N(), body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
    private static Formula Pred(Formula value) => App("InA033042", value);
    private static Formula A(Formula value) => App("a", value);
}
