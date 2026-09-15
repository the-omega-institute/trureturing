using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class YanevMaxExponentRadicalRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/YanevMaxExponentRadicalRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/yanev2017a051903");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum prime exponent drops by one when a positive integer greater than one is divided by its radical.",
        H("Yanev's Maximum Exponent Radical Recurrence"),
        Blocks(
            Paragraph(Text("N denotes the natural numbers including zero; all arithmetic and "
                + "the variables n and p are natural-valued. The finite set primeFactors(n) "
                + "contains the distinct prime divisors of n, and factorization(n,p) is the "
                + "exponent of p, zero outside that support. Mathlib takes both the prime-factor "
                + "set and factorization of zero to be empty. The named operator sup takes "
                + "a finite set and a natural-valued function and returns its maximum, "
                + "with value zero on the empty set. The expression "
                + "(p:N ↦ factorization(n,p)) denotes a function of p and makes "
                + "explicit the function underlying Lean's finitely supported factorization. "
                + "The value a(n) is the maximum exponent. The radical is the frozen "
                + "primeRadical of D5/S1/Deficit/AlmostAdditivity (A007947), the product of "
                + "distinct prime divisors, rendered as the named operator primeRadical. "
                + "The operator div means natural-number division, not field division.")),
            Paragraph(Text("OEIS A051903 defines a by the maximum prime exponent. "
                + "A007947 is primeRadical, and A003557(n) is n / primeRadical(n). The literature note "
                + "yanev2017a051903 records Labos Elemer's entry and Velin Yanev's "
                + "September 2, 2017 conjecture.")),
            Node("a", "The maximum prime exponent", MaximumFormula(),
                "The defining finite supremum is zero when the prime-factor set is empty. "
                + "In particular, a 0 = 0 is an out-of-range extension of the positive-index "
                + "OEIS sequence; a 1 = 0 is its stated base value.", DescribeRole.Definition),
            Node("result", "The A051903 base value, Yanev recurrence, and determination", ResultFormula(),
                "The first conjunct gives a 1 = 0. The radical is the frozen primeRadical "
                + "of D5/S1/Deficit/AlmostAdditivity (A007947), rendered as the named operator "
                + "primeRadical. For n > 1, division by this radical "
                + "subtracts one from every positive prime exponent. Extending the quotient's "
                + "factorization by zero to the original prime support preserves its supremum; "
                + "addition by one commutes with that nonempty supremum. This gives the "
                + "second conjunct for every natural n with 1 < n. The third conjunct states "
                + "that the relation together with a(1) = 0 determines the sequence on positive indices: "
                + "every function b:N → N with b(1) = 0 and the same recurrence agrees with a "
                + "at every n > 0. For n > 1, the radical divides n and is greater than one, "
                + "so its quotient is positive and strictly smaller than n. Strong induction "
                + "then gives agreement from the base value and the two recurrences.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a051903-yanev-max-exponent-radical-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a051903-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Bound(Formula variable) =>
        Seq(Forall, Sp, variable, Colon, Sp, Naturals(), Comma, Sp);
    private static Formula LambdaOverNaturals(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));

    private static Formula MaximumFormula()
    {
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula exponents = LambdaOverNaturals(p, Call("factorization", n, p));
        return Disp(Seq(Bound(n), Equal(Call("a", n),
            Call("sup", Call("primeFactors", n), exponents))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula b = F.Id("b");
        Formula quotient = Call("div", n, Call("primeRadical", n));
        Formula recurrence = Equal(Call("a", n), Add(Call("a", quotient), D(1)));
        Formula bAtOne = new Formula.Apply(b, [D(1)]);
        Formula bAtN = new Formula.Apply(b, [n]);
        Formula bAtQuotient = new Formula.Apply(b, [quotient]);
        Formula bRecurrence = Seq(Bound(n), Implication(Less(D(1), n),
            Equal(bAtN, Add(bAtQuotient, D(1)))));
        Formula agreement = Seq(Bound(n), Implication(Less(D(0), n),
            Equal(bAtN, Call("a", n))));
        Formula determination = Seq(Forall, Sp, b, Colon, Sp,
            Parenthesized(Seq(Naturals(), Sp, To, Sp, Naturals())), Comma, Sp,
            Implication(Equal(bAtOne, D(0)), Implication(bRecurrence, agreement)));
        return Disp(Conjunction(Equal(Call("a", D(1)), D(0)),
            Conjunction(Seq(Bound(n), Implication(Less(D(1), n), recurrence)),
                determination)));
    }
}
