using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA157100FiveTermRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/MatharA157100FiveTermRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2015a157100");
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, int k) => new Formula.Power(f, Num(k));
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula SumOf(params Formula[] fs) => fs.Aggregate(Add);
    private static Formula All(Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("n"), Nat, body);

    private static Formula Recurrence()
    {
        Formula n = F.Id("n");
        Formula qn = Par(Seq(n, Colon, Q));
        Formula An(int k) => Call("a", k == 0 ? n : Subtract(n, Num(k)));
        Formula equation = Equal(SumOf(
            Product(Par(Add(qn, Num(1))), An(0)),
            Product(Par(Add(Multiply(new Formula.Negate(Num(5)), qn), Num(1))), An(1)),
            Product(Num(2), Par(Subtract(Multiply(Num(2), qn), Num(1))), An(2)),
            Product(Num(2), Par(Subtract(Multiply(Num(2), qn), Num(7))), An(3)),
            Product(Num(2), Par(Add(Multiply(new Formula.Negate(Num(2)), qn), Num(7))), An(4))), Num(0));
        return All(new Formula.Logic(
            new Formula.Relation(Num(4), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.Implies, equation));
    }

    private static DocumentBlock Node(string name, string title, Formula body,
        AssessedProvenance provenance, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a157100-" + (name == "A" ? "series" : name)),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(body)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The five-term recurrence for the Catalan transform A157100.",
        H("The A157100 Catalan transform"),
        Blocks(
            Paragraph(Text("Work in ordinary formal power series over the rational numbers. "
                + "The symbol c denotes Mathlib's natural Catalan series, mapped coefficientwise "
                + "by the canonical homomorphism to Q. Its application to a series with zero "
                + "constant coefficient denotes formal substitution. All sequence indices are natural; "
                + "subtraction in a sequence argument is natural truncated subtraction. "
                + "All polynomial scalars in the recurrence are evaluated in Q.")),
            Node("A", "The source generating function",
                Equal(F.Id("A"), Product(Par(Add(Num(1), F.Id("X"))),
                    Call("c", Product(F.Id("X"), Par(Subtract(Num(1), Pow(F.Id("X"), 2))))))),
                AssessedProvenance.FromLiterature(Source),
                "OEIS A157100 FORMULA gives (1+x)*c(x*(1-x^2)), with c the generating function "
                + "of A000108. Formal substitution is defined because X*(1-X^2) has constant coefficient zero.",
                DescribeRole.Definition),
            Node("a", "The offset-zero coefficients",
                All(Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), F.Id("A")))),
                AssessedProvenance.FromLiterature(Source),
                "OEIS OFFSET 0,2 assigns index zero to the first coefficient. The rational "
                + "representation is the coefficient sequence of this exact generating function.",
                DescribeRole.Definition),
            Node("claim", "Mathar's five-term assertion",
                new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Recurrence()),
                AssessedProvenance.FromLiterature(Source),
                "The immutable OEIS record attributes the displayed identity to R. J. Mathar, "
                + "February 5, 2015. The source does not state an onset. Here n ≥ 4 is the maximal "
                + "well-formed interpretation under its offset-zero convention, not a quoted hypothesis. "
                + "Every such n is included; no eventual or finite-prefix substitute is used.",
                DescribeRole.Definition),
            Node("result", "The five-term recurrence", Recurrence(),
                AssessedProvenance.FromRepo(Source),
                "Apply the existing Catalan differential identity at t=X*(1-X^2) and use the "
                + "formal chain and product rules for A=(1+X)*c(t). Polynomial normalization gives "
                + "(1-5X+4X^2+4X^3-4X^4)*(X*A')+(1-4X+6X^2-2X^3-2X^4)*A=1-3X^2. "
                + "For every n ≥ 4 the forcing coefficient vanishes. The existing Euler coefficient "
                + "identity and the four shifts yield exactly the five displayed terms. "
                + "No Hankel-transform or Somos-4 assertion is part of this theorem.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a157100-five-term-recurrence"),
                    ResolutionKind.Proved)))));
}
