using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class SkoricTruncatedBinomialMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/skoric2021signatures");
    private const string SourceText = "Škorić, §6.2, Conjecture 1, equation (35), journal p.966. ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cap-normalized mean of an integer binomial row truncated to a positive cap is nonincreasing.",
        H("Škorić's truncated binomial mean"),
        Blocks(
            Node("f", Disp(All("x", Naturals(), All("r", Naturals(),
                Equal(Call("f", F.Id("x"), F.Id("r")), MeanBody(F.Id("x"), F.Id("r")))))),
                SourceText + "The displayed formula is the source's definition of f. " +
                "Both finite sums include w=0 and w=r. The upper argument x and cap r are natural numbers; " +
                "Nat.choose is the ordinary binomial coefficient, cast to ℝ before summation. " +
                "Division is in ℝ. Comparisons use positive caps, so the totalized value at r=0 is outside them.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                SourceText + "Here x ranges over integers at least two, and r and s are positive integer caps " +
                "with r<s and 2s≤x. Decrease is expressed as nonincrease, f(x,s)≤f(x,r). " +
                "The restriction 2s≤x expresses the source's r≤x/2 at the larger cap, without integer division.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", Disp(ClaimBody()),
                "For a positive row satisfying k·a(k)²≥(k+1)·a(k−1)·a(k+1), the adjacent " +
                "difference of normalized means has a positive numerator. Symmetrizing the product of " +
                "the two partial sums partitions it into convolution blocks. Monotonicity of the weighted " +
                "adjacent ratios controls every high block; the low block with index sum one contributes " +
                "a(0)·a(1)>0. Chaining adjacent comparisons and using the binomial recurrence proves " +
                "the stated comparison. This proves the scalar assertion used by source Propositions 1 and 2; " +
                "their other hypotheses and the protocol's security analysis are separate questions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("skoric-truncated-binomial-mean-" + name),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(formula),
            provenance, role == DescribeRole.Definition
                ? Blocks(SourceQuotation(), Paragraph(Text(prose)))
                : Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock SourceQuotation() => Paragraph(
        Text("Conjecture 1: “Let "), Math(In(Call("f", F.Id("x"), F.Id("r")))),
        Text(" be defined as” (equation (35)). “The function "),
        Math(In(Call("f", F.Id("x"), F.Id("r")))), Text(" is decreasing in "),
        Math(In(F.Id("r"))), Text(".”"));

    private static Formula MeanBody(Formula x, Formula r)
    {
        var w = F.Id("w");
        var coefficient = Cast(Apply(Qualified("Nat", "choose"), x, w), Reals());
        return Multiply(new Formula.Fraction(D(1), Cast(r, Reals())),
            new Formula.Fraction(
                PrefixSum(r, Multiply(Cast(w, Reals()), coefficient)),
                PrefixSum(r, coefficient)));
    }

    private static Formula PrefixSum(Formula r, Formula body) => Seq(
        Sum, Underscore, Grp(F.Id("w"), InMacro, Sp,
            Apply(Qualified("Finset", "range"), Add(r, D(1)))), Sp, body);

    private static Formula ClaimBody() => All("x", Naturals(), ImpliesTo(LeTo(D(2), F.Id("x")),
        All("r", Naturals(), ImpliesTo(LeTo(D(1), F.Id("r")),
            All("s", Naturals(), ImpliesTo(LtTo(F.Id("r"), F.Id("s")),
                ImpliesTo(LeTo(Multiply(D(2), F.Id("s")), F.Id("x")),
                    LeTo(Call("f", F.Id("x"), F.Id("s")), Call("f", F.Id("x"), F.Id("r"))))))))));

    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LeTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LtTo(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula ImpliesTo(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
