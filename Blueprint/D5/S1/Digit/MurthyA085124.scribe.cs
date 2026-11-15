using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class MurthyA085124Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/MurthyA085124.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/murthy2003a085124");
    private static readonly LibraryNoteRef Helper = LibraryNoteRef.Create("D5/L/Digit/ns2016zerofreemultiples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive terms of Murthy's decimal digit-product sequence have an exact classification.",
        H("Murthy's joint decimal divisibility classification"),
        Blocks(
            Paragraph(Text("Write P(N) for DigitProductSlices.digitProduct N, the product of "
                + "Nat.digits 10 N. These are the ordinary decimal digits, in reverse order, "
                + "with no leading zero. The product is independent of their order. "
                + "The explicit positive-N condition excludes the empty expansion of zero, "
                + "whose list product in Lean is one.")),
            Node("admissible", "The exact qualifying predicate", PredicateFormula(),
                "Both divisibilities have n on the left. Positivity of the product excludes "
                + "every zero digit. There is no bound on n, N, digit length or prime exponents.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a085124", "The least positive multiple, or zero", SequenceFormula(),
                "OEIS A085124, NAME: Smallest multiple of n whose digital product is also a "
                + "positive multiple of n, or 0 if no such number exists. Nat.find supplies "
                + "the least qualifying natural when the set is inhabited; the other branch "
                + "is zero. The source domain starts at n=1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Classification and full least-or-zero bridge", ResultFormula(),
                "For every positive natural n, existence is equivalent to all prime divisors "
                + "being at most seven and ten not dividing n. The same condition is equivalent "
                + "to positivity of the least-or-zero sequence. Its zero value means that no "
                + "qualifying integer exists; whenever positive, it qualifies and is at most "
                + "every qualifying N. This includes n=1: N=1 qualifies and the minimum is one. "
                + "For necessity, a prime divisor of n divides a nonzero decimal digit. A "
                + "multiple of ten has a terminal zero. For sufficiency write n=p^k m with "
                + "p either two or five, m coprime to ten and p^k coprime to m. The absence "
                + "of a factor ten permits this decomposition. N. S.'s digit lifting supplies "
                + "a zero-free k-digit suffix divisible by p^k, including the empty suffix "
                + "at k=0. Prepend the prime factors of n, with multiplicity, and a digit one "
                + "to make a nonempty block. The block product is divisible by n. Let b be "
                + "ten to its length. Euler's theorem modulo m(b-1), followed by the geometric "
                + "sum identity and cancellation of b-1, supplies a positive repetition count "
                + "for which m divides the repetition sum. Literal repetition preserves the "
                + "p^k divisibility, positive product and divisibility of that product by n. "
                + "All digit reconstruction and arithmetic are kernel checked for arbitrary "
                + "parameters. The suffix and repetition mechanism are prior work; their "
                + "use with a prime-factor word and the joint classification are a repository "
                + "derivation. The bounded literature screen found no exact resolution and "
                + "does not establish global novelty.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source, Helper)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("murthy-a085124-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Ex(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Nat, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Not(Formula a) => new Formula.Not(Par(a));
    private static Formula Q(Formula n, Formula v) => Call("admissible", n, v);
    private static Formula A(Formula n) => Call("a", n);
    private static Formula E(Formula n) => Ex("N", Q(n, F.Id("N")));
    private static Formula C(Formula n) => And(All("p", Imp(Call("Prime", F.Id("p")),
        Imp(Divides(F.Id("p"), n), Le(F.Id("p"), D(7))))), Not(Divides(D(1,0), n)));
    private static Formula PredicateFormula()
    {
        var n = F.Id("n"); var v = F.Id("N");
        return Disp(All("n", All("N", IffF(Q(n,v), And(Lt(D(0),v), And(Divides(n,v),
            And(Lt(D(0),Call("P",v)), Divides(n,Call("P",v)))))))));
    }
    private static Formula SequenceFormula()
    {
        var n = F.Id("n"); var v = F.Id("N");
        var set = Seq(OpenBrace, v, Sp, Colon, Sp, Nat, Sp, Mid, Sp, Q(n,v), CloseBrace);
        var cases = Seq(Begin, Grp(F.Id("cases")), Call("min",set), Amp, E(n), RowBreak,
            D(0), Amp, Not(E(n)), End, Grp(F.Id("cases")));
        return Disp(All("n", Equal(A(n), cases)));
    }
    private static Formula ResultFormula()
    {
        var n = F.Id("n"); var v = F.Id("N");
        return Disp(All("n", Imp(Lt(D(0),n), And(IffF(E(n),C(n)),
            And(IffF(Lt(D(0),A(n)),C(n)), And(IffF(Equal(A(n),D(0)),Not(E(n))),
                Imp(Lt(D(0),A(n)),And(Q(n,A(n)),All("N",Imp(Q(n,v),Le(A(n),v)))))))))));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
}
