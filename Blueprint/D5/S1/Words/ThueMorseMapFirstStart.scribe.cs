using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ThueMorseMapFirstStartDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ThueMorseMapFirstStart.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/joshirust2025monochromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First starts of longest Thue-Morse progressions at power-of-two differences.",
        H("First Longest Thue-Morse Progressions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thue-morse-map-definition"),
                DeclarationHandle.Create(Prefix + "MAP"),
                H("A progression in the actual word"),
                StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The word t is the zero-indexed binary digit-parity function thueMorse "
                    + "from ThueMorseReducedAbelianOdd, beginning 0110100110010110. "
                    + "False denotes 0 and true denotes 1. It satisfies t(0)=0, "
                    + "t(2u)=t(u), and t(2u+1)=1-t(u). MAP(d,s,L) says that the L "
                    + "letters at s, s+d, ..., s+(L-1)d all equal the letter at s. "
                    + "All indices and lengths are natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thue-morse-first-longest-definition"),
                DeclarationHandle.Create(Prefix + "FirstLongest"),
                H("An attained global maximum and its least start"),
                StatementSource.FromAuthor(FirstLongestFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "FirstLongest(d,s) requires an actual positive length L at s, "
                    + "bounds every progression length at every natural start by L, "
                    + "and excludes length L at every start smaller than s. Both "
                    + "letters are included because the letter is determined separately "
                    + "at each start. Thus L is the attained global maximum A(d), "
                    + "and s is its first attaining position i(d), in the sense of "
                    + "Joshi and Rust's Definitions 2.2, 2.3 and 2.5."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thue-morse-first-longest-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The three families of Conjecture 3.8"),
                StatementSource.FromAuthor(Disp(Equal(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every exponent e at least two, put q=2^e. At difference "
                    + "q+1 the first longest progression starts at 3q^2-q-1. "
                    + "At difference q-1 it starts at 3q^2-q+1 when e is even, "
                    + "and at q-1 when e is odd. The printed display in Section "
                    + "3.2.2 omits parameter ranges; e>=2 is the contextual reading "
                    + "from the immediately preceding maximum-length formulas. "
                    + "In the paper's three separate parameters this means n>=2 "
                    + "for the first equation and n>=1 for the other two. The known "
                    + "value i(3)=45 excludes extending the plus family to e=1; "
                    + "it is a previously known boundary exception."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thue-morse-first-longest-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The first starts for every exponent"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The positive maximum lengths are q+2 for q+1, q+4 for "
                        + "q-1 with even e, and q for q-1 with odd e. These maxima "
                        + "and the block-recognition principle are due to Aedo, "
                        + "Grimm, Nagai and Staynova, as cited by Joshi and Rust. "
                        + "The dyadic block and top parity identities are supplied by "
                        + "ThueMorseDyadic; the remaining required binary statements are proved inside this "
                        + "argument using the existing Thue-Morse word.")),
                    Paragraph(Text(
                        "Write a start as aq+b with 0<=b<q. Binary block parity "
                        + "gives t(aq+r)=t(a) xor t(r), and complementary residues "
                        + "control the carries and borrows. A length q+2 progression "
                        + "at difference q+1 forces s+q+1=kq^2 with k>=3; its next "
                        + "letter is opposite. For even e, a length q+4 progression "
                        + "at difference q-1 forces s+q=kq^2+1 with k>=3 and also "
                        + "has an opposite next letter. Block recognition excludes "
                        + "the half-block alternatives, including the boundary e=2. "
                        + "Explicit progressions at k=3 attain the claimed lengths. "
                        + "These facts prove the global bounds and exclude all "
                        + "earlier starts, for either letter.")),
                    Paragraph(Text(
                        "For odd e, let b=s mod q. The letters at progression "
                        + "indices b and b+1 are opposite, so no run has more than "
                        + "q letters. The start q-1 attains q letters. If s<q-1, "
                        + "then b=s and both opposite letters already occur among "
                        + "the first q positions. This excludes every earlier start. "
                        + "The proof applies to all exponents e>=2."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("joshi-rust-2025-thue-morse-first-longest-start"),
                    ResolutionKind.Proved)))));

    private static Formula MapFormula()
    {
        var d = F.Id("d");
        var s = F.Id("s");
        var length = F.Id("L");
        var j = F.Id("j");
        var letters = Bind(FormulaQuantifier.ForAll, "j",
            Implies(Less(j, length), Equal(Call("t", Add(s, Multiply(j, d))), Call("t", s))));
        return Disp(Bind(FormulaQuantifier.ForAll, "d",
            Bind(FormulaQuantifier.ForAll, "s", Bind(FormulaQuantifier.ForAll, "L",
                Iff(Call("MAP", d, s, length), letters)))));
    }

    private static Formula FirstLongestFormula()
    {
        var d = F.Id("d");
        var s = F.Id("s");
        var length = F.Id("L");
        var a = F.Id("a");
        var n = F.Id("N");
        var bound = Bind(FormulaQuantifier.ForAll, "a", Bind(FormulaQuantifier.ForAll, "N",
            Implies(Call("MAP", d, a, n), AtMost(n, length))));
        var first = Bind(FormulaQuantifier.ForAll, "a",
            Implies(Less(a, s), new Formula.Not(Call("MAP", d, a, length))));
        var attained = Bind(FormulaQuantifier.Exists, "L",
            And(Less(D(0), length), And(Call("MAP", d, s, length), And(bound, first))));
        return Disp(Bind(FormulaQuantifier.ForAll, "d", Bind(FormulaQuantifier.ForAll, "s",
            Iff(Call("FirstLongest", d, s), attained))));
    }

    private static Formula ClaimBody()
    {
        var e = F.Id("e");
        var q = new Formula.Power(D(2), e);
        var square = new Formula.Power(q, D(2));
        var baseStart = Subtract(Multiply(D(3), square), q);
        var plus = Call("FirstLongest", Add(q, D(1)), Subtract(baseStart, D(1)));
        var evenMinus = Implies(Call("Even", e),
            Call("FirstLongest", Subtract(q, D(1)), Add(baseStart, D(1))));
        var oddMinus = Implies(Call("Odd", e),
            Call("FirstLongest", Subtract(q, D(1)), Subtract(q, D(1))));
        return Bind(FormulaQuantifier.ForAll, "e",
            Implies(AtMost(D(2), e), And(plus, And(evenMinus, oddMinus))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
