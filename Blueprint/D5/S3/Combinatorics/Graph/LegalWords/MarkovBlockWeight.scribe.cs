using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class MarkovBlockWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/MarkovBlockWeight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered transition product of a legal binary block separates into a boundary "
        + "factor and a power of its occupation activity, and is strictly positive.",
        H("Legal Markov block weights and persistent mixture minors"),
        Blocks(
            Paragraph(Text(
                "A block w is a Boolean function on Fin n. The two exterior bits l and r "
                + "are observed separately. Adm on Fin.cons l (Fin.snoc w r) requires "
                + "every adjacent pair in this whole padded path to avoid two ones. "
                + "No endpoints are identified. Write k(w) for the sum of (w i).toNat, "
                + "where false.toNat is zero and true.toNat is one.")),
            Paragraph(Text(
                "The hard-core path-weight identity is classical; Lemma 6.1 of "
                + "Mukhamedov and Suhov gives its endpoint-dependent cylinder form. "
                + "Here their transition parameters are 1-p and p, their activity "
                + "is p/(1-p)^2, and their path is the padded block. Dividing their "
                + "cylinder mass by its positive initial stationary mass gives this "
                + "ordered transition product. For a parameter p, transition p has entries 1-p, p, 1, 0 in row order "
                + "(false,false), (false,true), (true,false), (true,true). "
                + "pathMass p n l w r is the actual ordered product from l through all "
                + "n bits of w to r. At n=0 it is transition p l r; at n+1 it is "
                + "transition p l (w 0) times pathMass p n (w 0) (Fin.tail w) r.")),
            Describe.Lean(DescribeId.Create("exact-path-weight"),
                DeclarationHandle.Create(Prefix + "path_weight_formula"),
                H("Boundary factor and activity at every positive length"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/mukhamedovsuhov2026hardcore")),
                Blocks(
                    Paragraph(Text(
                        "For every real p strictly between zero and one, every n at least "
                        + "one, both Boolean exterior bits and every legal padded block, "
                        + "the product equals the displayed expression and is strictly "
                        + "positive. Exponents are natural numbers; subtraction in the "
                        + "boundary exponent uses natural subtraction, and n+1 is at "
                        + "least l.toNat+r.toNat. With z=p/(1-p)^2, dependence on w "
                        + "is exactly z to the power k(w). The boundary factor depends "
                        + "only on p, n, l and r.")),
                    Paragraph(Text(
                        "Induct on the block length with the boundary exponent temporarily "
                        + "interpreted as an integer. The empty path has three allowed "
                        + "endpoint pairs, checked directly. At a new first bit, the "
                        + "false-false transition supplies one factor 1-p, false-true "
                        + "supplies p and one occupation, and true-false supplies one. "
                        + "The true-true case is excluded by Adm. Integer power addition "
                        + "accounts for the boundary shift; positivity of 1-p permits "
                        + "cancellation. At positive length the integer exponent agrees "
                        + "with the natural exponent. Every factor on the right is positive.")),
                    Paragraph(Text(
                        "The formula applies in particular to every component parameter "
                        + "between 1/3 and 3/8. It includes n=1 and forced boundary bits. "
                        + "For l=r=true and n=1, the only legal block is false and its "
                        + "mass is p. This gives the transition-product arithmetic for "
                        + "conditioning an interior interval. A full conditional law also "
                        + "needs cancellation of the exterior factors and normalization "
                        + "over legal completions. Blocks touching an open endpoint "
                        + "require their actual stationary endpoint factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("persistent-mixture-minor"),
                DeclarationHandle.Create(Prefix + "persistent_mixture_minor"),
                H("Positive explicit minor of normalized legal Markov mixtures"),
                StatementSource.FromAuthor(MinorFormula()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/mukhamedovsuhov2026hardcore")),
                Blocks(
                    Paragraph(Text(
                        "For every natural N, choose N+1 component parameters p in (0,1) "
                        + "strictly increasing in their Fin order, and positive weights t. "
                        + "The result therefore includes N at least two, parameters between "
                        + "1/3 and 3/8, and posterior weights summing to one. No weight-sum "
                        + "hypothesis is needed for this determinant identity. Both actual "
                        + "exterior bits l and r range independently over Bool.")),
                    Paragraph(Text(
                        "Let m=(2N+1)+(2N+1)=4N+2. pathNormalizer(p,m,l,r) sums "
                        + "pathMass over all Boolean length-m words whose padded path is "
                        + "Adm, assigning zero to every other word. activityPartition(p,m,l,r), "
                        + "written Z(p,m,l,r), sums z(p) to the occupation count over that "
                        + "same set, with z(p)=p/(1-p)^2. conditionalMixture(p,t,m,l,r,w) "
                        + "is the sum over components of t(k) times their actual pathMass "
                        + "divided by their pathNormalizer. Thus normalization uses the "
                        + "actual transition products and the full legal completion set.")),
                    Paragraph(Text(
                        "halfWord(N,j) is 0(10)^j followed by 2(N-j) zeros: at zero-based "
                        + "coordinate u it is true exactly when u is odd and u<2j. It has "
                        + "length 2N+1, starts and ends in zero, and contains exactly j ones. "
                        + "selectedWord(N,i,j) concatenates these two halves. Every selected "
                        + "word is legal for all four choices of exterior bits, including "
                        + "the seams and the middle cut, and has i+j ones. The map j to halfWord(N,j) is injective, since equal words have equal occupation counts. cutMinor(N,p,t,l,r) "
                        + "is the square matrix whose (i,j) entry is conditionalMixture "
                        + "at selectedWord(N,i,j), for i,j in Fin(N+1).")),
                    Paragraph(Text(
                        "The path-weight formula factors the positive boundary factor "
                        + "out of pathNormalizer, leaving Z. The completion set contains "
                        + "selectedWord(N,0,0), so Z is positive. Therefore the selected "
                        + "entry is the sum of c(k) z(p(k))^(i+j), where c(k)=t(k)/Z(p(k),m,l,r)>0. "
                        + "The explicit counting bijection sends each occupied coordinate "
                        + "2k+1 to k; adjacency and endpoint checks establish the legal-word "
                        + "bridge to these entries. With V(k,i)=z(p(k))^i, the matrix equals "
                        + "V-transpose times diag(c) times V. The Vandermonde determinant "
                        + "identity gives the displayed formula. The activity is strictly "
                        + "increasing on (0,1), so its nodes are distinct and the squared "
                        + "Vandermonde determinant is positive.")),
                    Paragraph(Text(
                        "This is the explicit-minor arithmetic for an interior block "
                        + "with both exterior observations present. It does not identify "
                        + "posterior weights from an entire complement, prove the stationary "
                        + "common-matrix representation, or establish the positive minimum "
                        + "of the rank-constrained discrepancy. Those require their separate "
                        + "probabilistic and compactness hypotheses. No fictitious exterior "
                        + "bits are assigned to open-endpoint blocks."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);


    private static Formula MinorFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), t = F.Id("t"), l = F.Id("l"), r = F.Id("r");
        Formula nat = Seq(Mathbb, Grp(F.Id("N"))), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula indices = Call("Fin", Add(n, D(1)));
        Formula functions = new Formula.TypeArrow(indices, real);
        Formula m = Add(Add(Mul(D(2), n), D(1)), Add(Mul(D(2), n), D(1)));
        Formula k = F.Id("k"), i = F.Id("i"), j = F.Id("j");
        Formula Range = All("k", indices, And(Less(D(0), Call("p", k)), Less(Call("p", k), D(1))));
        Formula Positive = All("k", indices, Less(D(0), Call("t", k)));
        Formula Activity(Formula x) => new Formula.Fraction(Call("p", x), Pow(Sub(D(1), Call("p", x)), D(2)));
        Formula coefficients = Seq(new Formula.Subscript(Prod, Seq(k, Colon, Sp, indices)), Sp,
            new Formula.Fraction(Call("t", k), Call("activityPartition", Call("p", k), m, l, r)));
        Formula gaps = Seq(new Formula.Subscript(Prod, Seq(i, Colon, Sp, indices)), Sp,
            new Formula.Subscript(Prod, Seq(j, InMacro, Sp, Call("Ioi", i))), Sp,
            Par(Sub(Activity(j), Activity(i))));
        Formula det = Call("det", Call("cutMinor", n, p, t, l, r));
        return Disp(All("n", nat, All("p", functions, All("t", functions,
            Imp(And(And(Range, Call("StrictMono", p)), Positive),
                All("l", Call("Bool"), All("r", Call("Bool"),
                    And(Call("Injective", Call("halfWord", n)),
                        And(Eq(det, Mul(coefficients, Pow(gaps, D(2)))), Less(D(0), det))))))))));
    }

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p"), n = F.Id("n"), l = F.Id("l"), r = F.Id("r"), w = F.Id("w");
        Formula nat = Seq(Mathbb, Grp(F.Id("N"))), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula q = Sub(D(1), p);
        Formula exponent = Sub(Sub(Add(n, D(1)), Call("toNat", l)), Call("toNat", r));
        Formula activity = new Formula.Fraction(p, Pow(q, D(2)));
        Formula occupation = Seq(new Formula.Subscript(Sum,
            Seq(F.Id("i"), Colon, Sp, Call("Fin", n))), Sp,
            Call("toNat", Call("w", F.Id("i"))));
        Formula mass = Call("pathMass", p, n, l, w, r);
        Formula rhs = Mul(Mul(Pow(p, Call("toNat", r)), Pow(q, exponent)),
            Pow(activity, occupation));
        Formula legal = Call("Adm", Add(n, D(2)), Call("cons", l, Call("snoc", w, r)));
        return Disp(All("p", real, Imp(And(Less(D(0), p), Less(p, D(1))),
            All("n", nat, Imp(Le(D(1), n), All("l", Call("Bool"),
                All("r", Call("Bool"), All("w", new Formula.TypeArrow(Call("Fin", n), Call("Bool")),
                    Imp(legal, And(Eq(mass, rhs), Less(D(0), mass)))))))))));
    }
}
