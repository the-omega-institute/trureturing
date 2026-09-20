using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class MbirikaAssociatedPellGcdEntryPointRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/MbirikaAssociatedPellGcdEntryPointRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/mbirika2023pellbraid");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The value k = 12 refutes the printed associated Pell gcd-entry-point biconditional.",
        H("The Associated Pell GCD Entry-Point Conjecture"),
        Blocks(
            Node("claim", "Mbirika-Schrader-Spilker Conjecture 32", ClaimFormula(),
                "Conjecture 32 states verbatim: \"We claim that gcd(Q_k, k) > 1 if and "
                    + "only if there exists a prime p such that p divides k and the rank "
                    + "of apparition (or entry point), e_Q(p) divides k. For example, "
                    + "gcd(Q_21, 21) = 7 and for the prime p = 7, we have p divides 21 "
                    + "and e_Q(p) = 3 divides 21.\" The symbol Q is the associated Pell "
                    + "sequence already defined in "
                    + "D5/S1/Recurrence/PellCompanionGcd, with initial values one and one. "
                    + "The existential r expresses that the least positive index where p "
                    + "divides Q exists, and that this index divides k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture fails at k = 12", ResultFormula(),
                "At k = 12, Q(12) = 19601 and gcd(Q(12),12) = 1, so the left side is "
                    + "false. The prime p = 3 divides 12, its least positive entry point "
                    + "is r = 2 because Q(1) = 1 and Q(2) = 3, and 2 divides 12. Thus "
                    + "the right side is true and the biconditional is false.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "mbirika-schrader-spilker-associated-pell-gcd-entry-point-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("mbirika-associated-pell-" + name),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ClaimFormula()
    {
        var k = F.Id("k");
        var p = F.Id("p");
        var r = F.Id("r");
        var s = F.Id("s");
        var qAtK = Call("Q", k);
        var left = Less(D(1), Call("gcd", qAtK, k));
        var minimal = All("s", Implies(
            Less(D(0), s),
            Implies(Less(s, r), new Formula.Not(Parenthesized(Divides(p, Call("Q", s)))))));
        var entryPoint = Exists("r", And(
            Less(D(0), r),
            Divides(p, Call("Q", r)),
            minimal,
            Divides(r, k)));
        var right = Exists("p", And(
            Call("Prime", p),
            Divides(p, k),
            entryPoint));
        var conjecture = All("k", Implies(
            LessOrEqual(D(1), k),
            Iff(left, right)));
        return Disp(Iff(F.Id("claim"), conjecture));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula All(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Exists(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
}
