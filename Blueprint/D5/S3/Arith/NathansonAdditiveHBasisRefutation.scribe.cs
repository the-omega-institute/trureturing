using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class NathansonAdditiveHBasisRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/NathansonAdditiveHBasisRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/nathanson2026hbases");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict inequality in Nathanson's Problem 12(2) fails for a three-element integer set.",
        H("Nathanson's Additive h-Basis Strict-Inequality Refutation"),
        Blocks(
            Paragraph(Text(
                "Here h \u2022 A denotes the h-fold sumset A + ... + A, with repetitions allowed. "
                    + "val denotes the coercion from natural numbers to integers. The expression "
                    + "sSup is the natural-number supremum. On the source domain used by the claim, "
                    + "the relevant sets are nonempty and bounded, so this supremum is a maximum.")),
            Paragraph(Text(
                "Problem 12. It is natural to ask how the use of negative numbers changes the size "
                    + "of the maximal interval [0, n] contained in an h-fold sumset. For integers "
                    + "h \u2265 2 and k \u2265 2, are the following statements true or false? (1) If A \u2208 "
                    + "(\u2124 choose k) with min(A) < 0, then \u2113_h(A) \u2264 n\u266d_h(k). (2) If A \u2208 "
                    + "(\u2124 choose k) with min(A) < 0, then \u2113_h(A) < n\u266d_h(k). Only statement "
                    + "(2) is settled here.")),
            Node("segment-length", "Largest covered initial segment", "segmentLength",
                SegmentLengthFormula(),
                "For h in N and a finite integer set A, segmentLength(h,A) is the largest natural "
                    + "n for which every natural i <= n, coerced to an integer, belongs to h \u2022 A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nonnegative-maximum", "Maximum over nonnegative k-sets", "nonnegativeMaximum",
                NonnegativeMaximumFormula(),
                "For h,k in N, nonnegativeMaximum(h,k) is the largest covered endpoint among all "
                    + "k-element finite subsets B of N. This is n\u266d_h(k).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("problem-twelve-two", "The strict universal claim", "claim",
                ClaimFormula(),
                "The claim quantifies h >= 2, k >= 2, and every k-element finite integer set A "
                    + "that contains a negative element and satisfies 0 in h \u2022 A. The last premise "
                    + "excludes exactly the cases in which the source leaves \u2113_h(A) undefined.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("problem-twelve-two-refuted", "Equality at a negative three-set", "result",
                ResultFormula(),
                "Take h=2, k=3, and A={-1,1,2}. Then 2A={-2,0,1,2,3,4}, so \u2113_2(A)=4. "
                    + "The set {0,1,2} shows n\u266d_2(3)>=4. Conversely, a three-element B subset N "
                    + "whose double sumset covers 0 through 5 must contain 0 and 1. Representing 3 "
                    + "forces its third element to be 2 or 3, but neither {0,1,2} nor {0,1,3} "
                    + "represents 5. Hence n\u266d_2(3)=4, contradicting the proposed strict inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nathanson-additive-h-bases-problem-12"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SegmentLengthFormula()
    {
        var h = F.Id("h");
        var a = F.Id("A");
        var n = F.Id("n");
        var i = F.Id("i");
        var cover = Universal("i", Naturals(), Implies(
            AtMost(i, n), Member(Call("val", i), Nsmul(h, a))));
        var body = Equal(Call("segmentLength", h, a), Call("sSup", SetOf(n, Naturals(), cover)));
        return Disp(UniversalMany([("h", Naturals()), ("A", Finset(Integers()))], body));
    }

    private static Formula NonnegativeMaximumFormula()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var n = F.Id("n");
        var b = F.Id("B");
        var i = F.Id("i");
        var cover = Universal("i", Naturals(), Implies(AtMost(i, n), Member(i, Nsmul(h, b))));
        var witness = Existential("B", Finset(Naturals()), And(
            Equal(Call("card", b), k), cover));
        var body = Equal(Call("nonnegativeMaximum", h, k),
            Call("sSup", SetOf(n, Naturals(), witness)));
        return Disp(UniversalMany([("h", Naturals()), ("k", Naturals())], body));
    }

    private static Formula ClaimFormula()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var aSet = F.Id("A");
        var a = F.Id("a");
        var negative = Existential("a", Integers(), And(Member(a, aSet), Less(a, D(0))));
        var quantifiedA = Universal("A", Finset(Integers()), Implies(
            Equal(Call("card", aSet), k),
            negative,
            Member(D(0), Nsmul(h, aSet)),
            Less(Call("segmentLength", h, aSet), Call("nonnegativeMaximum", h, k))));
        var quantified = UniversalMany([("h", Naturals()), ("k", Naturals())], Implies(
            AtMost(D(2), h), AtMost(D(2), k), quantifiedA));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Finset(Formula domain) => Call("Finset", domain);
    private static Formula Nsmul(Formula h, Formula set) => Call("nsmul", h, set);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula SetOf(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Existential(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);

    private static Formula UniversalMany((string Name, Formula Domain)[] variables, Formula body)
    {
        for (var index = variables.Length - 1; index >= 0; index--)
            body = Universal(variables[index].Name, variables[index].Domain, body);
        return body;
    }

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.Implies, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
