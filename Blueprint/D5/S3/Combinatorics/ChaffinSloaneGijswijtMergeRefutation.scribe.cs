using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ChaffinSloaneGijswijtMergeRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ChaffinSloaneGijswijtMergeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/chaffin2013curling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The starting sequence 1 2 refutes the merge identity once a 1 is allowed inside S.",
        H("A Two-Term Refutation of the Gijswijt Merge Identity"),
        Blocks(
            Node("curl-at-definition", "Ending in a repeated suffix", "IsCurlAt",
                IsCurlAtFormula(),
                "The last p k entries of s are k consecutive copies of the last p entries. "
                    + "Taking the suffix of length p as the repeated block loses nothing: any "
                    + "way of writing s as a prefix followed by k copies of a nonempty block "
                    + "of length p has that block equal to the suffix of length p.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("curl-definition", "Writing s as a prefix and k repetitions", "IsCurl",
                IsCurlFormula(),
                "Some nonempty block, of length at most the length of s, is repeated k times "
                    + "at the end of s.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("curling-number-definition", "The curling number", "cn",
                CurlingNumberFormula(),
                "The source defines the curling number of a sequence as the greatest k for "
                    + "which the sequence can be written as a prefix followed by k copies of "
                    + "a nonempty block. Every nonempty sequence admits k equal to one, so "
                    + "the supremum is attained and is at least one; the empty sequence "
                    + "admits no such k at all and the value one there is a convention that "
                    + "no statement below relies on.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step-definition", "One step of the process", "step",
                StepFormula(),
                "The source builds its sequences by repeatedly appending the curling number "
                    + "of what has been written so far.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("iterate-definition", "The sequence after t steps", "iter",
                IterateFormula(),
                "The source writes this as S with subscript t, the result of t appending "
                    + "steps applied to the starting sequence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("term-definition", "A single term of the continuation", "term",
                TermFormula(),
                "Entries are counted from zero. Performing n plus one steps produces a "
                    + "sequence of length greater than n, so the entry at position n is "
                    + "present and the default value is never used.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gijswijt-definition", "Gijswijt's sequence", "G",
                GijswijtFormula(),
                "The source's G, the continuation of the one-element sequence whose only "
                    + "entry is one. Its first eleven entries are 1, 1, 2, 1, 1, 2, 2, 2, 3, "
                    + "1, 1, and its first entry equal to four stands at position 220.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weakened-theorem", "The weakened merge identity", "claim",
                ClaimFormula(),
                "Theorem 23 of the source reads verbatim: \"Assume the curling number "
                    + "conjecture is true. Let S be an initial sequence not containing a 1, "
                    + "let S(e) be its 'extension' (defined in section 1), and let S(inf) be "
                    + "its infinite continuation. Then S(inf) = S(e) G.\" The last sentence "
                    + "of that section reads verbatim: \"We do not know if the theorem is "
                    + "still true if S is allowed to contain a 1 but does not end with 1.\" "
                    + "The statement displayed here is that weakened form. The tail length t "
                    + "carries the hypothesis that the extension exists, which is what the "
                    + "curling number conjecture would otherwise supply, so nothing here "
                    + "depends on that conjecture. The equality of infinite sequences is "
                    + "read off term by term.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weakened-theorem-refuted", "The weakened merge identity is false", "result",
                ResultFormula(),
                "Take S to be 1 2. It contains a 1 and does not end with 1. The curling "
                    + "number of 1 2 is one, so its tail length is zero and its extension is "
                    + "1 2 itself. The next entries are computed in turn: the curling number "
                    + "of 1 2 is 1, of 1 2 1 is 1, of 1 2 1 1 is 2, of 1 2 1 1 2 is 1, and of "
                    + "1 2 1 1 2 1 is 2, the last because that sequence is the square of "
                    + "1 2 1. So the continuation opens 1 2 1 1 2 1 2 2 2 3 while the "
                    + "extension followed by G opens 1 2 1 1 2 1 1 2 2 2, and the two differ "
                    + "at the seventh entry. The published argument breaks at exactly that "
                    + "point: it writes the continuation as W times X T to the power n "
                    + "followed by n, with the extension equal to W X and T a prefix of G, "
                    + "and for n equal to two it concludes from the first entry of X not "
                    + "being one. Here W is empty, X is 1 2, T is 1, and the first entry of "
                    + "X is one. Since the source states Theorem 23 under the curling number "
                    + "conjecture, its weakened form as an implication can still hold "
                    + "vacuously; what fails is the consequent, so that weakened form is "
                    + "equivalent to the negation of the curling number conjecture.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chaffin-sloane-gijswijt-merge-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Sequence() => F.Id("s");
    private static Formula Length(Formula value) => Call("length", value);

    private static Formula IsCurlAtFormula()
    {
        var s = Sequence();
        var p = F.Id("p");
        var k = F.Id("k");
        var block = Call("drop", s, Subtract(Length(s), p));
        var tail = Call("drop", s, Subtract(Length(s), Multiply(p, k)));
        var body = And(Less(D(0), p),
            And(LessEqual(Multiply(p, k), Length(s)),
                Equal(tail, Call("flatten", Call("replicate", k, block)))));
        return Disp(Universal("s", ListOfNaturals(),
            Universal("p", Naturals(),
                Universal("k", Naturals(),
                    Iff(Call("IsCurlAt", s, p, k), body)))));
    }

    private static Formula IsCurlFormula()
    {
        var s = Sequence();
        var p = F.Id("p");
        var k = F.Id("k");
        var body = Exists("p", Naturals(),
            And(LessEqual(p, Length(s)), Call("IsCurlAt", s, p, k)));
        return Disp(Universal("s", ListOfNaturals(),
            Universal("k", Naturals(), Iff(Call("IsCurl", s, k), body))));
    }

    private static Formula CurlingNumberFormula()
    {
        var s = Sequence();
        var k = F.Id("k");
        var admissible = SetBuilder(
            Seq(Typed(k, Naturals())),
            And(LessEqual(D(1), k),
                And(LessEqual(k, Length(s)), Call("IsCurl", s, k))));
        return Disp(Universal("s", ListOfNaturals(),
            Equal(Call("cn", s), Call("max", D(1), Call("sup", admissible)))));
    }

    private static Formula StepFormula()
    {
        var s = Sequence();
        return Disp(Universal("s", ListOfNaturals(),
            Equal(Call("step", s), Call("append", s, Call("singleton", Call("cn", s))))));
    }

    private static Formula IterateFormula()
    {
        var s = Sequence();
        var t = F.Id("t");
        var basis = Equal(Call("iter", D(0), s), s);
        var recursion = Equal(Call("iter", Add(t, D(1)), s), Call("step", Call("iter", t, s)));
        return Disp(Universal("s", ListOfNaturals(),
            Universal("t", Naturals(), Seq(basis, Sp, Sp, Sp, recursion))));
    }

    private static Formula TermFormula()
    {
        var s = Sequence();
        var n = F.Id("n");
        return Disp(Universal("s", ListOfNaturals(),
            Universal("n", Naturals(),
                Equal(Call("term", s, n),
                    Call("getD", Call("iter", Add(n, D(1)), s), n, D(0))))));
    }

    private static Formula GijswijtFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Naturals(),
            Equal(Call("G", n), Call("term", Call("singleton", D(1)), n))));
    }

    private static Formula ClaimFormula()
    {
        var s = Sequence();
        var t = F.Id("t");
        var r = F.Id("r");
        var m = F.Id("m");
        var conclusion = Universal("m", Naturals(),
            Equal(Call("term", s, Add(Add(Length(s), t), m)), Call("G", m)));
        var earlier = Universal("r", Naturals(),
            Implies(Less(r, t), NotEqual(Call("cn", Call("iter", r, s)), D(1))));
        var body = Universal("s", ListOfNaturals(),
            Universal("t", Naturals(),
                Implies(Member(D(1), s),
                    Implies(NotEqual(Call("getLast", s), D(1)),
                        Implies(Equal(Call("cn", Call("iter", t, s)), D(1)),
                            Implies(earlier, conclusion))))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula ListOfNaturals() => Call("List", Naturals());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula SetBuilder(Formula binder, Formula predicate) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Member(Formula element, Formula collection) =>
        Seq(element, Sp, InMacro, Sp, collection);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
