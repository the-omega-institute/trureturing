using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ThueMorseMapInfiniteFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ThueMorseMapInfiniteFibers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/joshirust2025monochromatic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinitely many exact global Thue-Morse maxima have infinite positive odd fibers.",
        H("Infinite Odd Fibers of Thue-Morse Maxima"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("thue-morse-exact-max"),
                DeclarationHandle.Create(Prefix + "ExactMax"),
                H("The attained global maximum"),
                StatementSource.FromAuthor(ExactMaxFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "MAP is reused from ThueMorseMapFirstStart, and thueMorse is the actual "
                    + "zero-indexed binary digit-parity word from ThueMorseReducedAbelianOdd. "
                    + "ExactMax(d,n) requires an attaining start and bounds every progression "
                    + "length at every natural start. The color at each start is unrestricted, "
                    + "so this maximum covers both letters of the entire infinite word."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thue-morse-infinite-fiber-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Question 3.7, second clause"),
                StatementSource.FromAuthor(Disp(Equal(F.Id("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Joshi and Rust ask whether infinitely many n have O_max(n)=infinity. "
                    + "For natural differences, their assertion is exactly that infinitely many "
                    + "lengths have infinitely many positive odd differences with attained "
                    + "global maximum equal to that length. Infinitude is displayed here by "
                    + "unbounded quantifiers on the natural numbers. The other two clauses "
                    + "of Question 3.7 are outside this statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thue-morse-infinite-fiber-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Infinitely many infinite fibers"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Fix odd m>=3, M=2^m, c=M^2+M+1, B=2^(4m+1)=2M^4, "
                        + "a=c(M^2-1), and U=2B+2. The shared dyadic_block and top_parity "
                        + "suppliers in ThueMorseDyadic give a true triple at a,a+c,a+2c "
                        + "inside one B block, and t(cj)=t(j) for j<M. Since B and c are "
                        + "coprime, residue transport puts a monochromatic triple inside "
                        + "every U-letter c-spaced window. Such a window cannot be a color "
                        + "translate of consecutive Thue-Morse letters, which have no "
                        + "monochromatic triple.")),
                    Paragraph(Text(
                        "For R=2^k>=2U+1,M and d=cR+1, divide any start by R. "
                        + "Among 2U+1 samples, either the first U precede the carry or U "
                        + "samples starting at the carry follow it. Binary block parity "
                        + "would make one of these segments the forbidden translated "
                        + "shadow. Thus every progression at every start has length at "
                        + "most 2U. Start zero attains length M. Maximizing the finite "
                        + "nonempty set of attained lengths gives an actual maximum in "
                        + "[M,2U], without assuming existence or using an explicit formula.")),
                    Paragraph(Text(
                        "The eligible exponents form an infinite tail, their positive "
                        + "odd differences are distinct, and the possible maxima are "
                        + "finite. Finite pigeonhole supplies an infinite exact-max fiber "
                        + "at some n>=M. Choosing m=2h+3 makes these lower bounds unbounded, "
                        + "which yields infinitely many such lengths. This proof supplies "
                        + "no formula for the selected maxima and makes no priority or "
                        + "external acceptance claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("joshi-rust-2025-thue-morse-infinite-odd-fibers"),
                    ResolutionKind.Proved)))));

    private static Formula ExactMaxFormula()
    {
        var d = F.Id("d"); var n = F.Id("n"); var s = F.Id("s"); var length = F.Id("L");
        var attained = Bind(FormulaQuantifier.Exists, "s", Call("MAP", d, s, n));
        var bound = Bind(FormulaQuantifier.ForAll, "s", Bind(FormulaQuantifier.ForAll, "L",
            Implies(Call("MAP", d, s, length), AtMost(length, n))));
        return Disp(Bind(FormulaQuantifier.ForAll, "d", Bind(FormulaQuantifier.ForAll, "n",
            Iff(Call("ExactMax", d, n), And(attained, bound)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var d = F.Id("d");
        var fiber = Bind(FormulaQuantifier.ForAll, "D", Bind(FormulaQuantifier.Exists, "d",
            And(Less(F.Id("D"), d), And(Less(D(0), d),
                And(Call("Odd", d), Call("ExactMax", d, n))))));
        return Bind(FormulaQuantifier.ForAll, "N", Bind(FormulaQuantifier.Exists, "n",
            And(Less(F.Id("N"), n), fiber)));
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
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
