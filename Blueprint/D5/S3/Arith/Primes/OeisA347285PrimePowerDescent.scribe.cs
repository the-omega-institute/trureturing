using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class OeisA347285PrimePowerDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/OeisA347285PrimePowerDescent.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PrimeForms/devlieger2021a347285");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descending prime-power exponents end at one, so their absolute first differences sum to n minus one.",
        H("De Vlieger's descending prime-power exponents"),
        Blocks(
            Paragraph(Text("The primes are indexed from one. The function prime is "
                + "D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative.prime, whose value at k is "
                + "Nat.nth Nat.Prime (k - 1). All row indices, exponents and lengths are natural numbers; "
                + "subtraction between them is truncated natural subtraction. Nat.floor rounds a real "
                + "number down to a natural number, returning zero for negative inputs. The casts "
                + "in the recurrence are to the reals; the casts in S and the conjecture are to the integers.")),
            Node("e", "The exponent recurrence", RecurrenceFormula(),
                "OEIS A347285, NAME (unpaginated): \"Irregular triangle T(n,k) starting with n followed by e_k = floor(log_p_k(p_(k-1)^e_(k-1))) such that e_k > 0.\" "
                + "FORMULA (unpaginated): \"T(n,1) = n; T(n,k) = floor(log_p_k(p_(k-1)^T(n,k-1))).\" "
                + "Here e n j is T(n,j+1); e extends the row through its first zero and thereafter. "
                + "The logarithm is Real.logb and the floor is Nat.floor.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("len", "The number of positive entries", LengthFormula(),
                "OEIS A347285, COMMENTS (unpaginated): \"T(0,1) = 0 by convention; 0 is not allowed for n > 0.\" "
                + "Together with \"such that e_k > 0\" in the NAME, this selects the positive entries. "
                + "The length is the first zero index; the displayed fallback is zero when no such index exists. "
                + "The proof establishes that a zero index exists for every n. At n=0, len is zero; "
                + "the separately listed source row {0} is outside the positive-row conjecture.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("S", "The absolute first differences", SumFormula(),
                "OEIS A347285, COMMENTS (unpaginated): \"Conjecture: let S be the sum of the absolute values of the first differences of terms in row n. For all n > 0, n - S = 1.\" "
                + "The index i ranges from zero through len n minus two. Int.natAbs makes each "
                + "integer difference a natural summand; the range is empty for a row of length at most one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "De Vlieger's conjecture", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A347285, COMMENTS (unpaginated): \"Conjecture: let S be the sum of the absolute values of the first differences of terms in row n. For all n > 0, n - S = 1.\" "
                + "The variable n ranges over all positive natural numbers. The final subtraction and equality are in the integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", Disp(ClaimBody()),
                "An exponent greater than zero strictly decreases at the next prime, because that prime is larger. "
                + "There is no infinite strictly descending sequence of natural numbers, so the row reaches zero. "
                + "Bertrand's postulate bounds the next prime by twice the current prime, hence by its square. "
                + "A positive exponent immediately before zero must therefore equal one. "
                + "Monotonicity turns each absolute difference into the preceding exponent minus the next, "
                + "and the sum telescopes from n to one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a347285-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula target) => Parenthesized(Seq(value, Colon, Sp, target));
    private static Formula Entry(Formula n, Formula j) => Call("e", n, j);
    private static Formula Prime(Formula k) => Call("prime", k);

    private static Formula RecurrenceFormula()
    {
        var n = F.Id("n");
        var j = F.Id("j");
        var next = Add(j, D(1));
        var power = new Formula.Power(Parenthesized(Cast(Prime(next), Reals)), Entry(n, j));
        var logarithm = Apply(Qualified("Real", "logb"), Cast(Prime(Add(j, D(2))), Reals), power);
        return Disp(new Formula.Aligned([
            All("n", Equal(Entry(n, D(0)), n)),
            All("n", All("j", Equal(Entry(n, next), Apply(Qualified("Nat", "floor"), logarithm))))
        ]));
    }

    private static Formula LengthFormula()
    {
        var n = F.Id("n");
        var j = F.Id("j");
        var exists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("j"), Nat,
            Equal(Entry(n, j), D(0)));
        var choice = Seq(Operatorname, Grp(F.Id("if")), Sp, F.Id("h"), Colon, Sp,
            Parenthesized(exists), Sp, Operatorname, Grp(F.Id("then")), Sp,
            Apply(Qualified("Nat", "find"), F.Id("h")), Sp, Operatorname, Grp(F.Id("else")), Sp, D(0));
        return Disp(All("n", Equal(Call("len", n), Parenthesized(choice))));
    }

    private static Formula SumFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var difference = Subtract(Cast(Entry(n, Add(i, D(1))), Ints), Cast(Entry(n, i), Ints));
        var summand = Apply(Qualified("Int", "natAbs"), Parenthesized(difference));
        var range = Apply(Qualified("Finset", "range"), Subtract(Call("len", n), D(1)));
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(All("n", Equal(Call("S", n), sum)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        return All("n", new Formula.Logic(
            Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n)),
            FormulaLogicOperator.Implies,
            Parenthesized(Equal(Subtract(Cast(n, Ints), Cast(Call("S", n), Ints)), D(1)))));
    }
}
