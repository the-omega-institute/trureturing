using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class DetlefsRoughResidueCharacterizationRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/DetlefsRoughResidueCharacterizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/sloane2011a008365");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime 17 refutes Detlefs's four-residue characterization of 13-rough numbers.",
        H("The OEIS A008365 Four-Residue Characterization of 13-Rough Numbers"),
        Blocks(
            Node("rough-numbers", "The 13-rough numbers", IsRough13Formula(),
                "For each natural n, isRough13(n) holds when every prime divisor p of n "
                    + "is at least 13.",
                "isRough13", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("four-residue-set", "Detlefs's four residue classes", InResidueSetFormula(),
                "For each natural n, inResidueSet(n) holds when its twenty-fourth power "
                    + "modulo 2310 is one of 1, 421, 631, and 841.",
                "inResidueSet", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("rough-residue-characterization", "Detlefs's rough-number characterization",
                ClaimFormula(),
                "For every positive natural n, the characterization identifies being "
                    + "13-rough exactly with membership in the four residue classes.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("rough-residue-characterization-refuted", "The characterization fails at 17",
                ResultFormula(),
                "The prime 17 is 13-rough, but its twenty-fourth power has residue 1681 "
                    + "modulo 2310, outside the four proposed classes. The five residues "
                    + "1, 421, 631, 841, and 1681 attained by 13-rough values are disclosed "
                    + "here without asserting the corrected characterization or its converse.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a008365-detlefs-rough-residue-characterization-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula IsRough13Formula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var divisorCondition = Implies(
            Call("Prime", p),
            Implies(
                new Formula.Relation(p, FormulaRelationOperator.Divides, n),
                LessThanOrEqual(D(1, 3), p)));
        return Disp(Universal("n", Iff(
            Call("isRough13", n),
            Universal("p", divisorCondition))));
    }

    private static Formula InResidueSetFormula()
    {
        var n = F.Id("n");
        var residue = new Formula.Modulo(
            new Formula.Power(n, D(2, 4)), D(2, 3, 1, 0));
        return Disp(Universal("n", Iff(
            Call("inResidueSet", n),
            Or(
                Equal(residue, D(1)),
                Equal(residue, D(4, 2, 1)),
                Equal(residue, D(6, 3, 1)),
                Equal(residue, D(8, 4, 1))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var characterization = Iff(
            Call("isRough13", n),
            Call("inResidueSet", n));
        var quantified = Universal("n", Implies(
            Less(D(0), n), characterization));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.Or, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
