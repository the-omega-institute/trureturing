using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class ActivityMeanCorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/ActivityMeanCorrespondence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly interior binary path means reconstruct positive activities, their product law, "
        + "and the partition function. Positive activities with the same means coincide.",
        H("Site activities and interior path means"),
        Blocks(
            Paragraph(Text(
                "The path has n+2 sites indexed from zero through n+1. Its legal Boolean words "
                + "have no consecutive true entries. The mean function u is strictly interior: "
                + "each used value lies between zero and one, and seam(u,i)=1-u(i)-u(i+1) "
                + "is positive on every adjacent edge. Only these finitely many means are used.")),
            Paragraph(Text(
                "The reconstructed activity at an internal site i is "
                + "u(i)(1-u(i))/(seam(u,i-1) seam(u,i)). At site zero it is u(0)/seam(u,0); "
                + "at site n+1 it is u(n+1)/seam(u,n). These endpoint formulas are exactly "
                + "the same expression with ghost means zero outside the path: the exterior "
                + "seams are 1-u at the endpoints and cancel the numerator factor 1-u. "
                + "The function activity constructs this finite vector with Fin.cons and Fin.snoc.")),
            Paragraph(Text(
                "For any activity vector w, monomial(w,b) is the product of w(i) raised to "
                + "the Boolean digit b(i). The function weight agrees with this product on "
                + "legal words and is zero elsewhere. The partition function sums weight "
                + "over all Boolean words, and law divides each weight by that sum. "
                + "Thus the normalization is defined by the actual configuration sum.")),
            Describe.Lean(DescribeId.Create("activity-mean-correspondence"),
                DeclarationHandle.Create(Prefix + "activity_mean_correspondence"),
                H("The product law, partition function, and unique inverse"),
                StatementSource.FromAuthor(Correspondence()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reconstructed activities are positive. Their normalized product "
                        + "law is the overlapping-table completion of u and consequently has "
                        + "every prescribed mean. Its partition function is the product of "
                        + "1-u over the n internal sites divided by the product of seam over "
                        + "the n+1 edges. Empty products equal one, so n=0 includes two-site paths.")),
                    Paragraph(Text(
                        "On a legal adjacent pair, the table entry factors as its empty-empty "
                        + "remainder times one factor for each occupied endpoint. Multiplying "
                        + "these edge factorizations and dividing the shared internal site "
                        + "tables combines exactly into the site activities. The remaining "
                        + "constant is emptyMass, the completion probability of the empty "
                        + "word. The normalized completion sums to one, hence emptyMass times "
                        + "the actual partition sum equals one. This determines the displayed "
                        + "normalization and identifies the whole product law.")),
                    Paragraph(Text(
                        "For any positive vector w, its product law has the prescribed interior "
                        + "means if and only if w is the explicitly reconstructed vector. "
                        + "There is no Markov assumption on w in this equivalence.")),
                    Paragraph(Text(
                        "For two positive product laws P and Q with the same means, expand "
                        + "their log probabilities into occupied-site log activities minus "
                        + "the log partition function. Equality of means and normalization "
                        + "make the sum of (P-Q)(log(P)-log(Q)) vanish. Every summand on legal "
                        + "words is nonnegative by strict monotonicity of the logarithm; "
                        + "both laws vanish on forbidden words. Therefore P and Q agree "
                        + "pointwise. Comparing the empty word identifies their partition "
                        + "functions, and comparing each singleton word identifies every "
                        + "activity. Applying this to the reconstructed law proves the equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-activity-means"),
                DeclarationHandle.Create(Prefix + "positive_activity_means"),
                H("Positive activities have interior means"),
                StatementSource.FromAuthor(InteriorMeans()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The function meansOf(w) is the occupied-state expectation at each "
                        + "path position and is extended by zero beyond the path. Every "
                        + "positive vector w has strictly interior means: singleton words "
                        + "give positive occupied-state probabilities, and the empty word "
                        + "gives positive vacancy probabilities and positive empty-empty "
                        + "edge remainders. Combining this with the preceding equivalence "
                        + "gives the correspondence in both directions, for all positive "
                        + "activity vectors and all strictly interior mean vectors."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Positive(Formula w, Formula n) => All("i", Call("Fin", Add(n, D(2))),
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, new Formula.Apply(w, [F.Id("i")])));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Correspondence()
    {
        Formula u = F.Id("u"), n = F.Id("n"), w = F.Id("w"), a = Call("activity", u, n);
        Formula law = Call("law", a), count = Add(n, D(1)), i = F.Id("i");
        Formula numerator = Seq(new Formula.Subscript(Prod, Seq(i, Colon, Sp, Call("Fin", n))), Sp,
            Grp(new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, Call("u", Add(Call("val", i), D(1))))));
        Formula denominator = Seq(new Formula.Subscript(Prod, Seq(i, Colon, Sp, Call("Fin", count))), Sp,
            Call("seam", u, Call("val", i)));
        Formula uniqueness = All("w", new Formula.TypeArrow(Call("Fin", Add(n, D(2))), Real()),
            Imp(Positive(w, n), new Formula.Logic(Call("Means", u, count, Call("law", w)),
                FormulaLogicOperator.Iff, Eq(w, a))));
        Formula conclusion = And(Positive(a, n), And(Eq(law, Call("completion", u, n)),
            And(Eq(Call("partition", a), new Formula.Fraction(numerator, denominator)),
                And(Call("Means", u, count, law), uniqueness))));
        return Disp(All("u", new Formula.TypeArrow(Nat(), Real()), All("n", Nat(),
            Imp(Call("Interior", u, Add(n, D(2))), conclusion))));
    }

    private static Formula InteriorMeans()
    {
        Formula n = F.Id("n"), w = F.Id("w"), means = Call("meansOf", w);
        return Disp(All("n", Nat(),
            All("w", new Formula.TypeArrow(Call("Fin", Add(n, D(2))), Real()),
                Imp(Positive(w, n), And(Call("Interior", means, Add(n, D(2))),
                    Call("Means", means, Add(n, D(1)), Call("law", w)))))));
    }
}
