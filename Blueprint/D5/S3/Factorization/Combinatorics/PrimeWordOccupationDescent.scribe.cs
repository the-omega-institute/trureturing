using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class PrimeWordOccupationDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Combinatorics/PrimeWordOccupationDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-word history is not recoverable, and word actions descend exactly when commuting.",
        H("Prime Word Occupation Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-prime-history-reconstruction"),
                DeclarationHandle.Create(Prefix + "no_prime_history_reconstruction"),
                H("No prime-history reconstruction"),
                StatementSource.FromAuthor(NoHistoryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ordered prime histories are lists of Mathlib prime subtypes, while the "
                        + "occupation state is their canonical multiset quotient. The words "
                        + "[2,3] and [3,2] have the same occupation state but are distinct, so "
                        + "no section can recover every original word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-descent-criterion"),
                DeclarationHandle.Create(Prefix + "order_descent_criterion"),
                H("Order descent criterion"),
                StatementSource.FromAuthor(DescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary input and state types, U assigns a state update to each "
                            + "input. The public witness is a dynamics on input "
                            + "multisets whose value on every list occupation is the imported "
                            + "left-to-right runWord action.")),
                    Paragraph(Text(
                        "Pairwise commutativity makes runWord invariant under list permutation "
                            + "and therefore defines the quotient dynamics. Conversely, applying "
                            + "any descended dynamics to the equal occupations of [p,q] and "
                            + "[q,p] forces the two updates to commute."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula NoHistoryFormula()
    {
        Formula prime = Call("Primes", Seq(Mathbb, Grp(F.Id("N"))));
        Formula word = F.Id("w");
        Formula section = F.Id("s");
        Formula words = Call("List", prime);
        Formula occupations = Call("Multiset", prime);
        return Disp(Seq(
            Neg, Sp, Exists, Sp, Typed(section, Arrow(occupations, words)), Comma, Sp,
            Forall, Sp, Typed(word, words), Comma, Sp,
            Apply(section, Call("occupation", word)), Sp, Eq, Sp, word, Dot));
    }

    private static Formula DescentFormula()
    {
        Formula prime = F.Id("P");
        Formula state = F.Id("X");
        Formula type = F.Id("Type");
        Formula update = F.Id("U");
        Formula descended = F.Id("V");
        Formula word = F.Id("w");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula wordType = Call("List", prime);
        Formula occupationType = Call("Multiset", prime);
        Formula updateType = Arrow(prime, Arrow(state, state));
        Formula descendedType = Arrow(occupationType, Arrow(state, state));
        Formula computation = Seq(
            Forall, Sp, Typed(word, wordType), Comma, Sp,
            Apply(descended, Call("occupation", word)), Sp, Eq, Sp,
            Call("runWord", update, word));
        Formula existsDescent = Seq(
            Exists, Sp, Typed(descended, descendedType), Comma, Sp,
            computation);
        Formula pairwiseCommute = Seq(
            Forall, Sp, Typed(Seq(p, Comma, Sp, q), prime), Comma, Sp,
            Call("Commute", Apply(update, p), Apply(update, q)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(prime, Comma, Sp, state), type), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(update, updateType), Comma, RowBreak, Grp(),
            Open, existsDescent, Close, Sp, Iff, Sp,
            Open, pairwiseCommute, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
