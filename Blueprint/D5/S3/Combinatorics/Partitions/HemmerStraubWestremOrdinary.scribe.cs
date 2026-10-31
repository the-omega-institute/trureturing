using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class HemmerStraubWestremOrdinaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both original ordinary HSW averages and their binomial value", H("Both original ordinary HSW averages and their binomial value"), Blocks(
            Paragraph(Text("ordinaryCharacter(mu,rho) is the complex linear trace of the independently constructed polytabloid representation spechtModuleComplex(mu) at a representative of the full positive cycle partition rho. The representative is selected from the permutation conjugacy class; its definition contains no Frobenius coefficient. The inherited same-partition ordinary-trace theorem supplies irreducibility and independence from the representative, with fixed points retained. The literal triplePartition removes zero rows and preserves the three original row lengths.")),
            Paragraph(Text("For a partition lambda of n, evTypes(lambda.parts.toList) is the original list of independent per-occurrence replacements a by (2a) or (a,a). It is kept as a list, including duplicate outcomes. Each occurrence tau is converted to its full partition of 2n using positivity and the doubled sum. leftTerm(lambda) sums (-1) to the length of tau times the ordinary character over every weakly decreasing even triple of size 2n, with zero padding. rightTerm(lambda) sums the ordinary character at the literal rectangle (n,n,0), for odd and even n alike. Attaching membership proofs to these lists and finite shape sets changes no multiplicity.")),
            Paragraph(Text("leftAverage(n) and rightAverage(n) sum those terms over every partition lambda of n with the rational weight inverse(zPartition(lambda)), then cast that rational weight into the complex numbers. The existing zPartition is the full product of k to multiplicity(k) times factorial(multiplicity(k)), with positive cycle sizes including one. The private rightCoefficientAverage is the literal rational rectangular Frobenius sum with the same Ev list and weight; rightAverage_eq_frobenius transports the actual trace sum to its complex cast. Integer coefficients are cast to the rationals before that final cast.")),
            Describe.Lean(DescribeId.Create("representative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.ordinaryCharacter_eq_trace"),
                H("Independence of the full-cycle representative"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), All("mu", Part(Id("n")), All("rho", Part(Id("n")), All("pi", Call("PermFin", Id("n")), Imp(Call("sameFullPartition", Id("pi"), Id("rho")), Eq(Call("ordinaryCharacter", Id("mu"), Id("rho")), Call("complexTrace", Call("spechtModuleComplex", Id("mu")), Id("pi")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("sameFullPartition states equality of the complete partition parts, including all fixed points."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pointwise"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.pointwise_identity"),
                H("Ordinary identity for each input partition"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), Imp(Call("positive", Id("n")), All("lambda", Part(Id("n")), Eq(Call("leftTerm", Id("lambda")), Call("rightTerm", Id("lambda")))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("The actual trace comparison is used in both terms before applying the existing HSW pointwise coefficient identity. No coefficient is defined to be an ordinary character."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weighted"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.weighted_identity"),
                H("Equality of the two ordinary weighted averages"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), Imp(Call("positive", Id("n")), Eq(Call("leftAverage", Id("n")), Call("rightAverage", Id("n"))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("The domain is every natural n at least one. The pointwise ordinary identity supplies equality of the averages. The final result below consumes this equality and the rectangular evaluation, giving the value of both original averages."))), DescribeRole.Theorem),
            WeightedDerivation(),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/HemmerStraubWestremOrdinary.result"),
                H("The full original ordinary-character conclusion"), StatementSource.FromAuthor(FullStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/hemmerstraubwestrem2025riordan")),
                Blocks(Paragraph(Text("The source endpoint is every n at least one, equality of the two averages and the displayed parity value for EACH average. It uses the actual same-partition complex polytabloid traces, with no desired identity, representation bridge or coefficient evaluation in its assumptions. The two derivative laws and the equal constant coefficients yield the generating-series identity, and exact coefficient extraction supplies the value for both averages."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hemmer-straub-westrem-2025-weighted-ev-character-average"), ResolutionKind.Proved)))));

    private static DocumentBlock WeightedDerivation() => new DocumentBlock.Section(
        H("The weighted coefficient derivation inside the ordinary consumer"), Blocks(
            Paragraph(Text("This is Conjecture 6.1, equation (6.1), of arXiv:2509.02796v1, and Conjecture 17, equation (6.1), page 15 of EJC 33 P1.57, DOI 10.37236/14401. The necessary proof components are reused from the exact published source at https://github.com/the-omega-institute/trureturing/blob/69f68474a0566d6f465a14259b74f28b58e293f3/D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.lean. The rectangular trace average is transported to the same exact Frobenius sum before this formal-series calculation is applied.")),
            Paragraph(Text("For arbitrary a_k in a commutative rational algebra, define A_n as the sum over every partition lambda of n of product(a_k^m_k)/z_lambda. Deleting a part k uses Mathlib Nat.Partition.partitionWithPartEquiv. The existing DeformedJucysMurphyC2.zExponent_add_single, at index k-1 and partitionExponent of the remaining partition, gives z_lambda = k m_k(lambda) z_nu; zExponent_pos permits cancellation in the rational weight. Summing the marked-part identity and using sum(k m_k) = n gives n A_n = sum from k=1 to n of a_k A_(n-k), with A_0 = 1. These are cycle_average_recursion, cycle_average_zero and cycle_average_derivative.")),
            Paragraph(Text("Set the coefficient ring to LaurentPolynomial Q, first = PowerSeries.mk (cycleAverage cycleInput), second = (1-t)^(-2)(1-tz)^(-2)(1-t/z)^(-2), and driver = PowerSeries.mk (fun k => cycleInput (k+1)), where cycleInput k = 2(z^k+1+z^(-k)). The direct call to LatticeHalfFockChargedCoefficients.solution_unique uses exactly those first, second and driver parameters. HasUniqueDiv.of_module_rat (LaurentPolynomial Q) supplies IsAddTorsionFree. The first derivative premise is cycle_average_derivative with multiplication commuted; the second is three_square_derivative with r=1, s=z, t=z^(-1), normalizing Laurent powers. Both coefficient-zero values are one, adapted through coeff_zero_eq_constantCoeff. This uniqueness principle requires additive torsion-freeness and does not require a new uniqueness argument for rational algebras.")),
            Paragraph(Text("The existing HemmerStraubWestrem.ev_right and right_coefficient, with triProd, give the rectangular Ev sum B_lambda = 2^r([X^n]P_lambda-[X^(n+1)]P_lambda), where P_lambda = product over all part occurrences a of (X^(2a)+X^a+1). Laurent substitution gives product(cycleInput a) = 2^r z^(-n) P_lambda(z), so B_lambda = CT((1-z^(-1)) product(cycleInput a)). Linearity of CT and the exact rational reciprocal zPartition weight identify rightCoefficientAverage with CT((1-z^(-1)) A_n). Its complex cast equals the independently defined ordinary rightAverage through rightTerm_eq_frobenius.")),
            Paragraph(Text("In G=(1-tz)^(-2)(1-t/z)^(-2), the coefficient expansion is sum_(i,j) (i+1)(j+1)t^(i+j)z^(i-j). Thus CT G = sum_j (j+1)^2 t^(2j), and CT(z^(-1)G) = t sum_j (j+1)(j+2)t^(2j). The standard binomial-series coefficients give sum_j (j+1)^2 q^j = 2(1-q)^(-3)-(1-q)^(-2) and sum_j (j+1)(j+2)q^j = 2(1-q)^(-3). At q=t^2, multiplying the difference by (1-t)^(-2) cancels (1-t)^2 and leaves (1-t^2)^(-3). The series manipulations are formal, with finite Laurent support at every t degree and unit constant coefficients; there is no analytic convergence premise.")),
            Paragraph(Text("Coefficient extraction now yields choose(n/2+2,2) when n is even, and zero when n is odd. The final proof transports that rational value into the complex trace average and uses weighted_identity for the left value. Every partition, original Ev occurrence and duplicate, full cycle including one, all weakly decreasing even triples and the literal rectangle (n,n,0) remain present. The n=0 generating-series coefficient is auxiliary; the external endpoint still quantifies n at least one. The N at least two identities and bijective proofs are separate questions."))));

    private static Formula FullStatement()
    {
        var n = Id("n");
        var left = Call("leftAverage", n);
        var right = Call("rightAverage", n);
        var half = Call("natDiv", n, new Formula.Number(2));
        var value = Call("parityValue", n, Call("choose", new Formula.Binary(half, FormulaBinaryOperator.Add, new Formula.Number(2)), new Formula.Number(2)));
        return Disp(All("n", Nat(), Imp(Call("positive", n), And(Eq(left, right), And(Eq(left, value), Eq(right, value))))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Seq(Operatorname, Grp(Id(name))) : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Part(Formula n) => Call("Partition", n);
}
