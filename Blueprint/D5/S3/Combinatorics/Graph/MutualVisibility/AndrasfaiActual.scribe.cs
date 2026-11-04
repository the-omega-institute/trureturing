using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class AndrasfaiActualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/AndrasfaiActual.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/howroyd2026a391632");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full original generating identity for all labelled mutual-visibility subsets of the Andrasfai graphs.",
        H("Actual subset counts and Howroyd's generating identity"),
        Blocks(
            Paragraph(Text("For every original n ≥ 1 put m = n - 1. The host has vertex set Z/(3m+2), with u adjacent to v exactly when the canonical representative of v-u is congruent to one modulo three. Thus it is Cay(Z/(3n-1), {1,4,...,3n-2}). A Configuration is any finite labelled vertex subset S such that every distinct pair in S admits a shortest path in this original host whose other vertices avoid S. The empty set and singletons are included. Write c(m) = Andrasfai.count m for the cardinality of this actual Configuration subtype; it is defined independently of any word or matrix.")),
            Describe.Lean(DescribeId.Create("configuration-word-equivalence"),
                DeclarationHandle.Create(Prefix + "configurationEquivPeriodicWord"),
                H("Actual configurations and labelled periodic words"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m ≥ 1, configurationEquivPeriodicWord m is an equivalence between Configuration(host m) and the subtype of functions labels : Fin (3m+2) → Bool for which PeriodicAvoidance(List.ofFn labels) holds. It restricts AndrasfaiWords.subsetLabelsEquiv using visible_iff_word_periodic_avoidance. Every vertex label and the origin are retained. PeriodicAvoidance excludes the entire forbidden family from every finite repetition, including factors crossing the labelled boundary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-count-trace"),
                DeclarationHandle.Create(Prefix + "count_eq_trace"),
                H("Uniform actual graph counts"), StatementSource.FromAuthor(CountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here M is AndrasfaiTransfer.transfer, the rational four-state labelled-edge matrix with entry two from state 3 to state 1. Cardinality transport along the actual configuration equivalence and AndrasfaiEnumeration.periodic_word_card_eq_trace give the equation. Its hypotheses hold because 3m+2 is positive and not divisible by three. The trace counts the full Boolean labelling, with the two labels on a shared edge counted separately."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-generating-series"),
                DeclarationHandle.Create(Prefix + "generatingSeries"),
                H("The series defined from original subset counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In Q[[X]], A = generatingSeries is defined as X times PowerSeries.mk(fun m => (Andrasfai.count m : Q)). Consequently its constant coefficient is zero, and for every original n ≥ 1 its coefficient at X^n is c(n-1), the number of all labelled actual visible subsets of the original graph. This is the formal meaning of the sum over n ≥ 1; it introduces no graph of index zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-trace-correction"),
                DeclarationHandle.Create(Prefix + "generatingSeries_eq_corrected_trace"),
                H("The original first coefficient"), StatementSource.FromAuthor(Disp(Eq(Call("generatingSeries"), Add(Call("traceSeries"), F.Id("X"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficients at all n ≥ 2 agree by count_eq_trace. At n = 1, AndrasfaiWords.count_zero gives four actual subsets of ZMod 2, whereas tr(M^2) is three. Hence exactly X must be added to the uncorrected traceSeries. Both constant coefficients are zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("howroyd-full-identity"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The full original rational identity"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Substitution into AndrasfaiTransfer.corrected_trace_series gives the entire numerator and denominator, including the original n = 1 coefficient. The denominator has constant coefficient one, and the displayed quotient denotes multiplication by its formal power-series inverse. The identity holds coefficientwise in Q[[X]], without analytic convergence assumptions. It counts all actual labelled existential shortest-path mutual-visibility subsets; it imposes no maximality, independence, or quotient condition."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a391632-andrasfai-mutual-visibility"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Paren(Formula f) => Seq(Open, f, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, byte b) => new Formula.Power(a, D(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CountFormula()
    {
        Formula m = F.Id("m");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula rat = Seq(Mathbb, Grp(F.Id("Q")));
        Formula condition = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, m);
        Formula lhs = Paren(Seq(Call("count", m), Sp, Colon, Sp, rat));
        Formula rhs = Call("trace", new Formula.Power(F.Id("M"), Add(Mul(D(3), m), D(2))));
        return Disp(Seq(Forall, Sp, Paren(Seq(m, Sp, Colon, Sp, nat)), Comma, Sp,
            new Formula.Logic(condition, FormulaLogicOperator.Implies, Eq(lhs, rhs))));
    }
    private static Formula ResultFormula()
    {
        Formula x = F.Id("X");
        Formula numerator = Add(Sub(Add(Sub(D(4), Mul(D(1,9), x)), Mul(D(3,3), Pow(x, 2))),
            Mul(D(4,0), Pow(x, 3))), Mul(D(8), Pow(x, 4)));
        Formula denominator = Add(Sub(Add(Sub(D(1), Mul(D(1,0), x)), Mul(D(2,9), Pow(x, 2))),
            Mul(D(3,2), Pow(x, 3))), Mul(D(8), Pow(x, 4)));
        return Disp(Eq(Call("generatingSeries"), new Formula.Fraction(Mul(x, Paren(numerator)), denominator)));
    }
}
