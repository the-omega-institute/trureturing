using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class MatharA128057ThreeTermRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2014a128057");
    private static Formula Q => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Series => Seq(Q, OpenBracket, OpenBracket, F.Id("X"), CloseBracket, CloseBracket);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Product(params Formula[] fs) => fs.Aggregate(Multiply);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Root(Formula s) => And(Equal(Call("constantCoeff", s), Num(1)),
        Equal(new Formula.Power(s, Num(2)), Add(Num(1), Product(Num(4), new Formula.Power(F.Id("X"), Num(2))))));
    private static Formula Inv(Formula s) => new Formula.Power(s, new Formula.Negate(Num(1)));
    private static Formula Coeff(Formula s, Formula n) => Call("coeff", n,
        Product(Par(Add(Num(1), F.Id("X"))), Inv(s)));

    private static Formula Statement()
    {
        Formula s = F.Id("S"), r = F.Id("R"), n = F.Id("n");
        Formula unique = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("S"), Series,
            And(Root(s), All("R", Series, Implies(Root(r), Equal(r, s)))));
        Formula qn = Par(Seq(n, Colon, Q));
        Formula recurrence = All("n", Nat, Implies(
            new Formula.Relation(Num(2), FormulaRelationOperator.LessThanOrEqual, n),
            Equal(Add(Add(
                Product(qn, Par(Subtract(Product(Num(5), qn), Num(9))), Coeff(s, n)),
                Product(Num(4), Coeff(s, Subtract(n, Num(1))))),
                Product(Num(4), Par(Subtract(Product(Num(5), qn), Num(4))),
                    Par(Subtract(qn, Num(2))), Coeff(s, Subtract(n, Num(2))))), Num(0))));
        Formula inverse = And(Equal(Call("constantCoeff", Inv(s)), Num(1)),
            And(Equal(Product(s, Inv(s)), Num(1)),
                And(Equal(Product(Inv(s), s), Num(1)), recurrence)));
        return And(unique, All("S", Series, Implies(Equal(Call("constantCoeff", s), Num(1)),
            Implies(Equal(new Formula.Power(s, Num(2)),
                Add(Num(1), Product(Num(4), new Formula.Power(F.Id("X"), Num(2))))), inverse))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-term recurrence for the normalized square-root quotient A128057.",
        H("The A128057 square-root quotient"),
        Blocks(
            Paragraph(Text("Work in ordinary formal power series Q[[X]]. There is a unique S with "
                + "constant coefficient 1 and S²=1+4X². For every such S, its inverse is normalized "
                + "and is a two-sided unit inverse. Set A=(1+X)S⁻¹ and a(n)=coeff n A. "
                + "The formula below expands these two local definitions. Sequence indices are natural; "
                + "subtraction inside a coefficient index is natural truncated subtraction. Every scalar "
                + "polynomial, including 5n-9 and n-2, is evaluated in Q.")),
            Describe.Lean(DescribeId.Create("a128057-result"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result"),
                H("The normalized root, its inverse, and the three-term recurrence"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("OEIS A128057 gives the generating function (1+x)/sqrt(1+4x²) "
                        + "and attributes the three-term conjecture to R. J. Mathar. Its offset is zero. "
                        + "The source does not specify an onset: n≥2 here is the legal-lag interpretation, "
                        + "not a quoted source hypothesis. Every such n is included.")),
                    Paragraph(Text("Let c be the Catalan series rescaled by -1. The existing Catalan "
                        + "identity gives Xc²+c=1, so B=1+2Xc satisfies B²=1+4X. Its derivative "
                        + "companion D=(Xc)' satisfies BD=1. Expansion X↦X² constructs S=B(X²), "
                        + "and the two square-root branches are separated by the constant coefficient. "
                        + "The coefficients of D are b(m)=(-1)^m binomial(2m,m); thus a(2m)=a(2m+1)=b(m). "
                        + "The existing adjacent central-binomial identity gives "
                        + "(m+1)b(m+1)+2(2m+1)b(m)=0. Splitting n into even and odd cases and "
                        + "normalizing rational polynomial arithmetic yields the displayed recurrence.")),
                    Paragraph(Text("Mathar's paper on P-finite recurrences includes A128057 in Example 4 "
                        + "and provides a general method. The bounded passage inspection recorded with "
                        + "the source identifies no explicit settlement of this exact shorter recurrence; "
                        + "global or implicit prior settlement is unmeasured. No global novelty claim is made."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a128057-three-term-recurrence"), ResolutionKind.Proved)))));
}
