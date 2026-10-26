using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA365771Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/hanna2023a365771");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base-five digit descent proves Hanna's first residue and the shared classification.",
        H("Hanna's Catalan-binomial residues modulo five"),
        Blocks(
            Paragraph(Text("The sequence is a product of a Catalan quotient and a binomial coefficient. "
                + "All indices and arithmetic operations below are in Nat. Nat.div denotes natural "
                + "integer division; subtraction is truncated at zero. The quotient in a is exact. "
                + "The digit predicate includes zero. OEIS entries have no page numbers; quotations "
                + "refer to A365771 revision 23, Name and Comments, and A033042, Name.")),
            Node("a", "The sequence", All("n", Equal(A(F.Id("n")), SequenceBody(F.Id("n")))),
                "a(n) = binomial(2*n+1, n)/(2*n+1) * binomial(3*n-1, n) for n >= 0. "
                + "The index n is a natural number, including zero; Nat.choose denotes binomial.", false, true),
            Node("InA033042", "Sums of distinct powers of five",
                All("m", new Formula.Logic(P(Pred(F.Id("m"))), FormulaLogicOperator.Iff, P(DigitBody(F.Id("m"))))),
                "Sums of distinct powers of 5. The value m is in A033042 exactly when every "
                + "digit in Nat.digits 5 m is zero or one. The offset is zero: 0, 1, 5, 6, 25.", false, true),
            Node("claim", "Hanna's first conjecture",
                new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, P(ClaimBody())),
                "Conjectures: given A033042 is the sums of distinct powers of 5, then "
                + "(1) a(5*A033042(n)) == 4 (mod 5) for n > 0, "
                + "Here m ranges over the positive values of A033042, rather than their enumeration indices.", false, true),
            Node("digits_step", "Removing the last base-five digit", DigitStep(),
                "For positive n the digit condition separates into the last digit being at most one "
                + "and the same condition on Nat.div n 5.", true, false),
            Node("residue_classification", "The complete positive-index classification", Classification(),
                "Lucas decomposition makes Nat.choose (3*n) n * Nat.choose (2*n) n congruent "
                + "to the indicator of the digit predicate. Strong induction on n proves this through "
                + "division by five. The exact identity 3*(n+1)*a(n)=2*M(n), where M is that "
                + "binomial product, determines the residue at last digits zero through three. "
                + "At last digit four, Nat.choose (3*n-1) n vanishes modulo five directly by Lucas. "
                + "The resulting classification is used by all three congruences.", true, false),
            Node("result", "Hanna's first congruence", ClaimBody(),
                "Multiplication by five appends a zero base-five digit. The classification "
                + "therefore gives residue four for every positive m with digits zero or one.", true, false))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool theorem, bool literature, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("hanna365771-" + (name == "InA033042" ? "in-a033042" : name == "digits_step" ? "digits-step" : name == "residue_classification" ? "residue-classification" : name)),
        DeclarationHandle.Create("D5/S1/Recurrence/Residue/HannaA365771." + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition, resolution);

    private static Formula SequenceBody(Formula n) => Multiply(
        Q("Nat", "div", Q("Nat", "choose", Add(Multiply(D(2), n), D(1)), n),
            Add(Multiply(D(2), n), D(1))),
        Q("Nat", "choose", Subtract(Multiply(D(3), n), D(1)), n));
    private static Formula DigitBody(Formula m) => All("d", Imp(
        new Formula.Relation(F.Id("d"), FormulaRelationOperator.MemberOf, Q("Nat", "digits", D(5), m)),
        new Formula.Relation(F.Id("d"), FormulaRelationOperator.LessThanOrEqual, D(1))));
    private static Formula ClaimBody() => All("m", Imp(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
        Imp(Pred(F.Id("m")), Equal(Mod(A(Multiply(D(5), F.Id("m")))), D(4)))));
    private static Formula DigitStep() => All("n", Imp(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
        new Formula.Logic(P(Pred(F.Id("n"))), FormulaLogicOperator.Iff, P(And(
            new Formula.Relation(Mod(F.Id("n")), FormulaRelationOperator.LessThanOrEqual, D(1)),
            Pred(Q("Nat", "div", F.Id("n"), D(5))))))));
    private static Formula Classification() => All("n", Imp(
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id("n")),
        Equal(Mod(A(F.Id("n"))), If(Pred(F.Id("n")),
            If(Equal(Mod(F.Id("n")), D(0)), D(4), D(2)), D(0)))));
    private static Formula If(Formula test, Formula yes, Formula no) => Seq(
        Operatorname, Grp(F.Id("if")), Sp, P(test), Sp,
        Operatorname, Grp(F.Id("then")), Sp, P(yes), Sp,
        Operatorname, Grp(F.Id("else")), Sp, P(no));
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula P(Formula value) => Parenthesized(value);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Q(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), N(), body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.Implies, P(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(P(left), FormulaLogicOperator.And, P(right));
    private static Formula Mod(Formula value) => new Formula.Modulo(P(value), D(5));
    private static Formula Pred(Formula value) => App("InA033042", value);
    private static Formula A(Formula value) => App("a", value);
}
