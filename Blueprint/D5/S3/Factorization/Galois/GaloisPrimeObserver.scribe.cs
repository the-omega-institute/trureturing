using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GaloisPrimeObserverDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Galois/GaloisPrimeObserver.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tagged Frobenius observer has an infinite unramified fiber.",
        H("Galois Prime Observers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frobenius-observation-has-infinite-fiber"),
                DeclarationHandle.Create(
                    Prefix + "frobenius_observation_has_infinite_fiber"),
                H("A finite Frobenius output merges infinitely many unramified primes"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The named galoisPrimeObserver returns none on the ramified branch "
                            + "and some conjugacy class on the unramified branch. This tag "
                            + "prevents a total Frobenius value from being asserted at every "
                            + "prime.")),
                    Paragraph(Text(
                        "The named mathlibFrobeniusAt is the local bridge. On an unramified "
                            + "ideal it returns the class of Mathlib's arithFrobAt; on a "
                            + "ramified ideal it returns none. No parallel Frobenius theory "
                            + "is introduced.")),
                    Paragraph(Text(
                        "The strong infinite pigeonhole theorem first supplies an infinite "
                            + "fiber of the tagged observer. Finiteness of the ramified set "
                            + "rules out none, leaving an infinite fiber labeled by some "
                            + "Frobenius conjugacy class.")),
                    Paragraph(Text(
                        "The proof uses only a monoid with finitely many conjugacy classes. "
                            + "It does not assume fields, a number field, or a finite group; "
                            + "those structures belong only to the Mathlib bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-ramification-is-necessary"),
                DeclarationHandle.Create(Prefix + "finite_ramification_is_necessary"),
                H("All-ramified tagging refutes the unramified-fiber conclusion"),
                StatementSource.FromAuthor(RamificationNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the trivial group and tag every rational prime as ramified. The "
                        + "ramified set is infinite, the observer is constantly none, and "
                        + "every some-class fiber is empty. This is the concrete counterexample "
                        + "for omitting finite ramification."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-conjugacy-output-is-necessary"),
                DeclarationHandle.Create(
                    Prefix + "finite_conjugacy_output_is_necessary"),
                H("An infinite conjugacy-class output can preserve prime identity"),
                StatementSource.FromAuthor(OutputNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the commutative monoid Multiplicative Nat, whose conjugacy-class "
                            + "quotient is infinite, and send each rational prime to the class "
                            + "of its underlying natural number. Commutativity makes the class "
                            + "map injective, so every fiber is finite.")),
                    Paragraph(Text(
                        "The degenerate audit also covers the opposite endpoint: for the "
                            + "trivial group, the unramified observer is constant and its sole "
                            + "class has all rational primes as an infinite fiber. A monoid's "
                            + "conjugacy-class output cannot be empty because it contains the "
                            + "class of one."))),
                DescribeRole.Lemma))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Fiber(Formula observer, Formula value)
    {
        Formula prime = F.Id("p");
        Formula primes = F.Id("Primes");
        Formula observed = Seq(observer, Open, prime, Close);
        Formula taggedValue = Call(F.Id("some"), value);
        return Seq(
            OpenBrace, prime, Sp, InMacro, Sp, primes, Sp, Mid, Sp,
            observed, Sp, Eq, Sp, taggedValue, CloseBrace);
    }

    private static Formula MainFormula()
    {
        Formula group = F.Id("G");
        Formula observer = F.Id("O");
        Formula value = F.Id("c");
        Formula classes = Call(F.Id("ConjClasses"), group);
        Formula taggedClasses = Call(F.Id("Option"), classes);
        Formula observerType = new Formula.TypeArrow(F.Id("Primes"), taggedClasses);

        return Disp(Seq(
            Forall, Sp, group, Comma, Sp,
            Call(F.Id("Finite"), classes), Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, observer, Colon, Sp, observerType, Comma, Sp,
            Call(F.Id("Finite"), Call(F.Id("RamifiedPrimes"), observer)), Sp,
            Rightarrow,
            RowBreak, Grp(),
            Exists, Sp, value, InMacro, Sp, classes, Comma, Sp,
            Call(F.Id("Infinite"), Fiber(observer, value)), Dot));
    }

    private static Formula RamificationNecessityFormula()
    {
        Formula observer = F.Id("R");
        Formula value = F.Id("c");
        Formula classes = Call(F.Id("ConjClasses"), F.Id("Unit"));
        Formula noInfiniteClassFiber = Seq(
            Neg, Exists, Sp, value, InMacro, Sp, classes, Comma, Sp,
            Call(F.Id("Infinite"), Fiber(observer, value)));
        return Disp(Seq(
            Call(F.Id("Infinite"), F.Id("RamifiedPrimes")), Sp, Land, Sp,
            noInfiniteClassFiber, Dot));
    }

    private static Formula OutputNecessityFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula monoid = Call(F.Id("Multiplicative"), naturals);
        Formula classes = Call(F.Id("ConjClasses"), monoid);
        Formula observer = F.Id("J");
        Formula value = F.Id("c");
        return Disp(Seq(
            Call(F.Id("Infinite"), classes), Sp, Land, Sp,
            Neg, Exists, Sp, value, InMacro, Sp, classes, Comma, Sp,
            Call(F.Id("Infinite"), Fiber(observer, value)), Dot));
    }
}
