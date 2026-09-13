using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class KrehMinimalSetLayerGrowthRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/KrehMinimalSetLayerGrowthRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/kreh2015minimalsets");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An infinite decimal-subsequence set has minimal-layer sizes 1, 2, and then 1 forever.",
        H("Kreh's Minimal-Set Layer-Growth Conjecture"),
        Blocks(
            Node(
                "kreh-digit-subsequence",
                "The decimal-string subsequence order",
                "digitSubseq",
                DigitSubseqFormula(),
                "The decimal digit lists are reversed into printed order. Thus "
                    + "digitSubseq(a,b) is Kreh's decimal-subsequence relation: the printed decimal "
                    + "string of a is obtained from that of b by deleting zero or more digits.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kreh-minimal-elements",
                "Minimal elements of a set",
                "minimal",
                MinimalFormula(),
                "An element a is retained precisely when it lies in M and every element "
                    + "of M whose decimal string is a subsequence of a equals a itself.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kreh-peeling-sequence",
                "Successive removal of minimal elements",
                "peel",
                PeelFormula(),
                "The zeroth layer is M. Each successor layer removes exactly the "
                    + "minimal elements of the preceding layer.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kreh-minimal-layer-size",
                "The size of a minimal layer",
                "eta",
                EtaFormula(),
                "The value eta(M,k) is the finite-cardinality operator ncard applied to "
                    + "the minimal elements after k peelings. For an infinite set, ncard "
                    + "equals zero; the counterexample does not rely on that convention, "
                    + "because its layers are proved to be singletons or a pair.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kreh-divergent-layer-claim",
                "The asserted divergence of minimal-layer sizes",
                "claim",
                ClaimFormula(),
                "The positivity premise expresses Kreh's convention that N contains the "
                    + "positive integers. For every infinite M with eta(M,0) below eta(M,1), "
                    + "the conclusion says that every natural bound eventually holds for "
                    + "all later layer sizes.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "kreh-divergent-layer-claim-refuted",
                "The divergence claim is false",
                "result",
                Disp(new Formula.Not(F.Id("claim"))),
                "For M* = {1, 10, 11} union {110*10^j : j is natural}, the first "
                    + "minimal set is {1}, the next is {10, 11}, and the remaining set "
                    + "after k+2 peelings is the tail beginning at 110*10^k. Its minimal "
                    + "set is the first element of that tail, so the layer sizes are "
                    + "1, 2, 1, 1, and then 1 forever. The countability sentence of "
                    + "Conjecture 18 is not asserted here.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kreh-2015-minimal-sets-conjecture-18"),
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
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula DigitSubseqFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula left = Call("digitSubseq", a, b);
        Formula right = OperatorCall(
            "Sublist",
            OperatorCall("reverse", OperatorCall("digits", D(1, 0), a)),
            OperatorCall("reverse", OperatorCall("digits", D(1, 0), b)));
        return Disp(AllNat(["a", "b"], Equivalent(left, right)));
    }

    private static Formula MinimalFormula()
    {
        Formula set = F.Id("M"), a = F.Id("a"), b = F.Id("b");
        Formula minimality = AllNat(
            ["b"],
            Implies(
                Member(b, set),
                Implies(Call("digitSubseq", b, a), Equal(b, a))));
        Formula members = Seq(
            OpenBrace, a, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            And(Member(a, set), minimality), CloseBrace);
        return Disp(AllSet(Equal(Call("minimal", set), members)));
    }

    private static Formula PeelFormula()
    {
        Formula set = F.Id("M"), k = F.Id("k");
        Formula zero = Equal(Call("peel", set, D(0)), set);
        Formula successor = AllNat(
            ["k"],
            Equal(
                Call("peel", set, Add(k, D(1))),
                Seq(
                    Call("peel", set, k), Sp, Setminus, Sp,
                    Call("minimal", Call("peel", set, k)))));
        return Disp(AllSet(And(zero, successor)));
    }

    private static Formula EtaFormula()
    {
        Formula set = F.Id("M"), k = F.Id("k");
        Formula value = Equal(
            Call("eta", set, k),
            OperatorCall("ncard", Call("minimal", Call("peel", set, k))));
        return Disp(AllSet(AllNat(["k"], value)));
    }

    private static Formula ClaimFormula()
    {
        Formula set = F.Id("M"), n = F.Id("n"), bound = F.Id("B");
        Formula cutoff = F.Id("N"), k = F.Id("k");
        Formula positive = AllNat(
            ["n"],
            Implies(Member(n, set), Less(D(0), n)));
        Formula divergent = AllNat(
            ["B"],
            ExistsNat(
                "N",
                AllNat(
                    ["k"],
                    Implies(
                        AtMost(cutoff, k),
                        AtMost(bound, Call("eta", set, k))))));
        Formula body = Implies(
            positive,
            Implies(
                Call("Infinite", set),
                Implies(
                    Less(Call("eta", set, D(0)), Call("eta", set, D(1))),
                    divergent)));
        return Disp(Equivalent(F.Id("claim"), Parenthesized(AllSet(body))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula AllSet(Formula body) => Seq(
        Forall, Sp, F.Id("M"), Sp, Subseteq, Sp, Naturals(), Comma, Sp, body);

    private static Formula AllNat(string[] names, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Naturals()))],
            body);

    private static Formula ExistsNat(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula OperatorCall(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Iff,
            Parenthesized(right));
}
