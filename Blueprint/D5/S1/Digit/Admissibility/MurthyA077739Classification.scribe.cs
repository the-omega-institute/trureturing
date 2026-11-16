using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class MurthyA077739ClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Admissibility/MurthyA077739Classification.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Digit/murthy2002a077739");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete decimal prefix, suffix, divisibility and digit-sum classification in OEIS A077739.",
        H("Murthy's A077739 Classification"),
        Blocks(
            Paragraph(Text("OEIS A077739 defines a(n) as the smallest positive multiple of n "
                + "beginning and ending with the usual decimal expansion of n and having digit sum n, "
                + "or zero if no such number exists. The source conjecture says that the zero indices "
                + "are exactly 11, 17 and 19. The statement below concerns every natural n at least one; "
                + "there is no bound on the value or decimal length of the multiple. Decimal expansions "
                + "have no leading zeros, may have interior zeros, and their prescribed ends may overlap.")),
            Paragraph(Text("Generality I records the concrete decimal certificate rows consumed below 1000. "
                + "The symbolic tail and final assertion remain unbounded in n and witness length; "
                + "no classification for arbitrary numeral bases is asserted.")),
            Paragraph(Text("Write s(x) for the sum of Nat.digits 10 x and w(x) for that list's length. "
                + "A positive N begins in n exactly when N=n times 10^k+r for some k,r with 0<=r<10^k. "
                + "It ends in n exactly when N modulo 10^w(n) equals n. These conditions allow k=0 "
                + "and do not require the two ends to be disjoint. The predicate Witness conjoins "
                + "positivity, n dividing N, s(N)=n, and these two positional conditions. "
                + "Admissible(n) means that some N satisfies Witness(n,N).")),
            Node("digitSum", "Decimal digit sum", DefinitionFormula("digitSum", "sumDigits10"),
                "Nat.digits lists digits from least to most significant; their sum is independent of that order.",
                DescribeRole.Definition),
            Node("a", "The source's least-or-zero sequence", SequenceFormula(),
                "The natural infimum of the witness set is its least member when nonempty, and zero "
                + "when empty. Every member is positive. Nat.sInf_mem and Nat.sInf_eq_zero therefore "
                + "prove a(n)=0 exactly when Admissible(n) is false; this is the well-ordering bridge "
                + "from the existence construction to the actual source sequence.", DescribeRole.Definition),
            Node("result", "The complete least-or-zero classification", ResultFormula(),
                "Concatenating multiples of n preserves divisibility and adds digit sums. Start and end "
                + "with a literal n block. For L with n<=10^L, the multiple B_L=n(10^L-1) "
                + "has digit sum 9L: write it as (n-1)10^L+(10^L-n), with the lower block padded to "
                + "L digits. Its complement identity follows by decimal recursion. For n>=1000, put "
                + "d=w(n)>=4. Induction gives 9d^2+81d<=10^(d-1)<=n, and s(n)<=9d. Congruence "
                + "modulo nine gives the integer q=(n-10s(n))/9>=d(d-1). Set b=q mod d and "
                + "a=floor(q/d)-b; then q=ad+b(d+1). The blocks n, eight additional copies of n, "
                + "a copies of B_d, b copies of B_(d+1), and a final n give a positive witness "
                + "with digit sum 10s(n)+9ad+9b(d+1)=n. This is an unbounded symbolic construction. "
                + "For 10<=n<1000 outside the three exceptions, the retained certificate records "
                + "multiplicities of blocks jn. Kernel reduction checks that their digit sums total "
                + "n-2s(n), and the general block construction supplies the witness. The certificate arrays MurthyA077739CertificateLow.entries and "
                + "MurthyA077739CertificateHigh.entries retain indices 0..499 and 500..999; "
                + "certificateData appends them in that order. The certificate uses j<=195 and 1643 multiplier-count pairs; n=18 uses an empty middle. For "
                + "1<=n<=9, take N=n. No certificate failure proves nonexistence. "
                + "For 11, the suffix forces N=11+100q, s(q)=9, and 11 dividing q. Evaluating "
                + "q's digits at -1 yields a multiple of 11 between -9 and 9 which is odd, a "
                + "contradiction. For 17 and 19, a zero-length appended block gives digit sum 8 "
                + "or 10; a one-digit overlap is impossible. With disjoint ends, write "
                + "N=n10^(k+2)+100M+n. For 19 the ends already contribute 20. For 17 the middle "
                + "has sum one, so M=10^j; divisibility would make 17 divide a power of ten, "
                + "contradicting primality. These arguments cover all lengths and all overlaps. "
                + "Combining existence, the three exclusions, and the infimum bridge proves the "
                + "whole source claim. No minimal witness values beyond existence are asserted. "
                + "The public OEIS source still presents this as a conjecture in the supplied revision. "
                + "The bounded repository, pinned Mathlib and public-source search located no full "
                + "classification in its examined scope; third-party coverage is incomplete and "
                + "this document makes no priority or exhaustive novelty claim. The general certificate "
                + "soundness theorem consumes the finite data, and the terminal classification consumes "
                + "both that bounded branch and the symbolic tail; the table alone is not the result. "
                + "The source-equivalence Reg registration retains exact source reconstruction, lawful "
                + "template enrollment, whole-family variation and sensitivity, and actual observational "
                + "dependence. Its continuation is unknown, which does not assert undecidability. "
                + "The result does not compute least positive witnesses, classify other bases, or settle "
                + "new external questions. A qualified successor remains pending literature screening.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a077739-murthy-zero-indices"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("murthy-a077739-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(statement),
            name == "a" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula DefinitionFormula(string name, string expression) =>
        Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), F.Id("Nat"),
            EqFormula(Call(name, F.Id("n")), Call(expression, F.Id("n")))));

    private static Formula SequenceFormula() =>
        Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), F.Id("Nat"),
            EqFormula(Call("a", F.Id("n")), Call("sInf", Call("positiveWitnessSet", F.Id("n"))))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var exceptions = new Formula.Logic(EqFormula(n, D(1, 1)), FormulaLogicOperator.Or,
            new Formula.Logic(EqFormula(n, D(1, 7)), FormulaLogicOperator.Or, EqFormula(n, D(1, 9))));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), F.Id("Nat"),
            new Formula.Logic(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n),
                FormulaLogicOperator.Implies,
                new Formula.Logic(EqFormula(Call("a", n), D(0)), FormulaLogicOperator.Iff, exceptions))));
    }

    private static Formula EqFormula(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [..args]);
}
