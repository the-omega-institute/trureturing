using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA365771ZeroDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/hanna2023a365771");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's third congruence modulo five.",
        H("Hanna's third congruence modulo five"),
        Blocks(
            Paragraph(Text("The natural-number sequence a and the predicate InA033042 are those of "
                + "HannaA365771. InA033042 includes zero and means that every base-five digit is "
                + "at most one. Division and subtraction use natural arithmetic. OEIS entries have "
                + "no page numbers; the source is A365771 revision 23, Comments, and A033042, Name.")),
            Describe.Lean(DescribeId.Create("hanna365771-zero-claim"),
                DeclarationHandle.Create("D5/S1/Recurrence/Residue/HannaA365771Zero.claim"),
                H("Hanna's third conjecture"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"),
                    FormulaLogicOperator.Iff, P(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("(3) a(n) == 0 (mod 5) for n > 0 except when n or n-1 equals 5*A033042(k) for some k >= 0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hanna365771-zero-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Residue/HannaA365771Zero.result"),
                H("Hanna's third congruence"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If every base-five digit of a positive n is zero or one, division by five gives a quotient m in A033042 and remainder zero or one. Thus n=5*m or n-1=5*m. Outside these two forms, the positive-index residue classification gives residue zero."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna365771-mod5-zero"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody() => All("n", Imp(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
        Imp(Seq(Neg, Sp, P(new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("m"), N(), And(Pred(F.Id("m")), Or(
                Equal(F.Id("n"), Multiply(D(5), F.Id("m"))),
                Equal(Subtract(F.Id("n"), D(1)), Multiply(D(5), F.Id("m")))))))),
            Equal(new Formula.Modulo(P(A(F.Id("n"))), D(5)), D(0)))));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Or, P(right));
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
