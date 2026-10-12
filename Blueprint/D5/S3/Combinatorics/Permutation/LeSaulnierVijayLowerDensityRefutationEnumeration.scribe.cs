using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class LeSaulnierVijayLowerDensityRefutationEnumerationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationEnumeration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective natural ranking of an infinite set determines a literal enumeration.",
        H("Enumeration in increasing rank"),
        Blocks(Describe.Lean(
            DescribeId.Create("enumeration-in-increasing-rank"),
            DeclarationHandle.Create(Prefix + "enumerateRank"),
            H("An enumeration increasing in an injective rank"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every infinite subset S of the natural numbers and every natural-valued "
                + "function rank injective on S, there is an injective map pi from the natural "
                + "numbers onto S with rank(pi(i)) strictly increasing in i. Enumerate the "
                + "infinite image rank(S) by Mathlib's Nat.nth, then select its unique preimages "
                + "in S. Infinite(S) and InjOn(rank,S) denote these two hypotheses; "
                + "Injective(pi) and range(pi)=S state the literal permutation conclusion."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var s = F.Id("S");
        var rank = F.Id("rank");
        var pi = F.Id("pi");
        var i = F.Id("i");
        var j = F.Id("j");
        var functionType = new Formula.TypeArrow(Naturals(), Naturals());
        var conclusion = And(Call("Injective", pi),
            Equal(Call("range", pi), s),
            All("i", Naturals(), All("j", Naturals(),
                Imp(Less(i, j), Less(Call("rank", Call("pi", i)),
                    Call("rank", Call("pi", j)))))));
        return Disp(All("S", Call("Set", Naturals()),
            All("rank", functionType,
                Imp(And(Call("Infinite", s), Call("InjOn", rank, s)),
                    new Formula.Bind(FormulaQuantifier.Exists,
                        FormulaIdentifier.Create("pi"), functionType, conclusion)))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));
}
