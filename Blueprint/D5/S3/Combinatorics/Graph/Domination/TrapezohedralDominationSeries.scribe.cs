using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TrapezohedralDominationSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TrapezohedralDominationSeries.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/oeis2026a381190");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original A381190 rational generating function for all n>=3.",
        H("The complete formal generating series"), Blocks(
            Paragraph(Text("The coefficient ring is Q and x is the formal indeterminate X. The actualSeries coefficient of order n is the rational cast of actualCount n. Thus its coefficients at orders 0, 1 and 2 vanish, and every order n>=3 counts the original actual labelled subsets. No convergence, eventual recurrence, finite extrapolation, actual-count hypothesis or replacement graph is used.")),
            Describe.Lean(DescribeId.Create("series"), DeclarationHandle.Create(Prefix + "actualSeries"),
                H("The literal actual-count series"), StatementSource.FromAuthor(Disp(All("n", Nat,
                    Eq(Call("coeff", V("n"), Call("actualSeries")), Call("castToQ", Call("actualCount", V("n"))))))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("This is PowerSeries.mk applied to the rational actual-count sequence. castToQ denotes the natural-number cast into Q."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-series"), DeclarationHandle.Create(Prefix + "actual_series"),
                H("The original polynomial and squared denominator"), StatementSource.FromAuthor(Disp(SeriesFormula())),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Let M count native path maximal independent subsets and r the endpoint-restricted count with the zero prefix. The proved inverse head/tail maps give M(n+3)=M(n+1)+M(n), with M(0)=M(1)=1 and M(2)=2. The inverse endpoint/middle maps give r(n+4)+M(n)=M(n+4), and r(3)=1. Coefficientwise formal identities yield F(1-x^2-x^3)=1+x+x^2 and R(1-x^2-x^3)=x^3+2x^4+2x^5. The actual-set bijections give actualSeries=2xR'. Differentiating the second identity and multiplying by the unit denominator proves the displayed expression. In Lean the fraction is multiplication by the inverse of the squared power-series denominator; its constant coefficient is 1, so this is the literal rational formal series. All hypotheses are discharged by actual set constructions and the entire count sequence is included."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381190-trapezohedral-domination-series"),
                    ResolutionKind.Proved))),
        []));

    private static Formula SeriesFormula()
    {
        Formula x = Call("X");
        Formula p = Sub(Sub(Sub(Add(Add(Mul(D(4), Pow(x, 5)), Mul(D(8), Pow(x, 4))),
            Mul(D(4), Pow(x, 3))), Mul(D(9), Pow(x, 2))), Mul(D(8), x)), D(3));
        Formula numerator = Mul(Mul(Seq(Minus, D(2)), Pow(x, 3)), Par(p));
        Formula denominator = Pow(Sub(Add(Pow(x, 3), Pow(x, 2)), D(1)), 2);
        return Eq(Call("actualSeries"), new Formula.Fraction(numerator, denominator));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, byte n) => Seq(Par(a), Caret, Grp(D(n)));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
}
