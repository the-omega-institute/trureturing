using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class OnnisSquareThreeStepRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/OnnisSquareThreeStepRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/onnis2022happyv1");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive perfect square first reaches one after three iterations of the "
            + "nonzero-decimal-digit-product square map.",
        H("Onnis's Square Convergence Prohibition Is False"),
        Blocks(
            Node("onnis-nonzero-digit-product", "Nonzero decimal digit product",
                "nonzeroDigitProduct", ProductFormula(),
                "P(n) is the product of exactly the nonzero entries of Nat.digits 10 n. "
                    + "Mathlib stores digits from least to most significant; multiplication "
                    + "in the natural numbers is commutative, so this is the source's "
                    + "decimal digit product. Zeros are removed, rather than multiplied.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onnis-nonzero-digit-step", "The square map", "step", StepFormula(),
                "Section 1.2 squares the product P(n), and repeats this map on the result. "
                    + "The definition applies to every natural input; the conjecture's "
                    + "domain consists of positive inputs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onnis-sequence-membership", "Sequence membership", "SequenceMember",
                MemberFormula(),
                "A positive integer belongs to the sequence when a finite iterate reaches "
                    + "one. Iteration zero is the initial value itself. Iteration is "
                    + "mathlib's Function.iterate, with no auxiliary orbit restriction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onnis-first-hitting-time", "Exact convergence length", "FirstHit",
                FirstHitFormula(),
                "FirstHit(n,t) requires the value one at index t and excludes one at "
                    + "every earlier natural index, including index zero. Repeated terminal "
                    + "ones do not increase the first hitting time.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onnis-square-convergence-claim", "The whole Section 3 conjecture", "claim",
                ClaimFormula(),
                "The original prohibition quantifies over all positive natural squares "
                    + "that are sequence members. The existential root is any natural "
                    + "number. There is no restriction to smooth roots or squares in the "
                    + "image of a preceding digit-product step.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onnis-square-three-step-refuted", "A square with first hitting time three",
                "result", Disp(new Formula.Not(F.Id("claim"))),
                "The square 235^2 = 55225 has successive nonzero digit products 500, "
                    + "10 and 1. Their squares give 55225 -> 250000 -> 100 -> 1. "
                    + "Nat.digits_ofDigits proves each decimal representation with its "
                    + "digit bounds and nonzero last digit. The iterate successor equations "
                    + "give the three transitions; indices zero, one and two have values "
                    + "different from one. Hence the positive square is a sequence member "
                    + "with exact first hitting time three, contradicting the whole "
                    + "Section 3 conjecture. This makes no assertion about Section 4's "
                    + "separate at-most-three statement, least examples or image-restricted "
                    + "families, and makes no historical-priority claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("onnis-2022-square-three-step-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ProductFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Eq(Call("P", n),
            Call("prod", Call("FilterNonzero", Call("digits", D(1, 0), n))))));
    }

    private static Formula StepFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Eq(Call("step", n), Pow(Call("P", n), D(2)))));
    }

    private static Formula MemberFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Iff(Call("SequenceMember", n),
            Exists("t", Eq(Iter(F.Id("t"), n), D(1))))));
    }

    private static Formula FirstHitFormula()
    {
        var n = F.Id("n");
        var t = F.Id("t");
        var k = F.Id("k");
        return Disp(All("n", All("t", Iff(Call("FirstHit", n, t),
            And(Eq(Iter(t, n), D(1)), All("k",
                Implies(Lt(k, t), new Formula.Not(Eq(Iter(k, n), D(1))))))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        return Disp(Iff(F.Id("claim"), All("n",
            Implies(Lt(D(0), n),
                Implies(Exists("r", Eq(n, Pow(F.Id("r"), D(2)))),
                    Implies(Call("SequenceMember", n),
                        new Formula.Not(Call("FirstHit", n, D(3)))))))));
    }

    private static Formula All(string name, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, body);

    private static Formula Exists(string name, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, body);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula body) =>
        new Formula.BindMany(quantifier,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name),
                Seq(Mathbb, Grp(F.Id("N"))))], body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);

    private static Formula Iter(Formula t, Formula n) => Call("Iterate", F.Id("step"), t, n);

    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);

    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);

    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);

    private static Formula Implies(Formula a, Formula b) =>
        Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
}
