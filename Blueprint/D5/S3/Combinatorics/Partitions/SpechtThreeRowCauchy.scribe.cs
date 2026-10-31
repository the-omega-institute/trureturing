using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtThreeRowCauchyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite Cauchy calculation and actual three-row traces", H("The finite Cauchy calculation and actual three-row traces"), Blocks(
            Paragraph(Text("Use six variables Xi,Yj indexed by the disjoint union of two copies of Fin 3. An edge (i,j) has weight k at Xi and k at Yj, with all other exponents zero. Its geometric series has coefficient one exactly at these edge weights. Multiplication by 1-XiYj gives one: the shifted coefficients cancel except at the zero monomial. Define K as the product of these nine labelled series. There is no analytic convergence condition.")),
            Paragraph(Text("The coefficient of K at X^a Y^b, when the natural row margin a has total n, is the cardinality of the existing finite set contingencyTables(n,a,b). Indeed, the product coefficient formula indexes decompositions of the six-variable exponent into nine edge weights. The exponent on edge (i,j) is its table entry A(i,j); the decomposition equation is precisely the three row and three column equations. Sending a decomposition to its Xi coordinate on each edge and sending a table to its nine edge monomials are inverse maps. The total-table equation follows by summing the row margins. Unequal column total gives the empty set automatically.")),
            Paragraph(Text("For any commutative ring and elements xi,yj, let dij=1-xi*yj. The matrix whose i-th row is [di1*di2,di0*di2,di0*di1] has determinant Delta(x)Delta(y), by the three-by-three determinant formula and the polynomial ring identity. If dij*qij=1, scaling row i of q by di0*di1*di2 gives this numerator matrix. The product of the nine d's times the product of the nine q's equals one. It follows that Delta(x)Delta(y) times the product of the qij equals det(q). Applying this to the nine geometric series proves Delta(X)Delta(Y)K=det((1-XiYj) inverse). No character or Schur orthogonality enters this argument.")),
            Paragraph(Text("A term of the determinant selects one edge from each row and column. The coefficient at X^u Y^v in the product of the three selected geometric series is one if u(i)=v(s(i)) for every i and zero otherwise. Its exponent decomposition, when it exists, is unique: the Xi coordinate fixes the exponent on the selected edge. If u and v are strictly decreasing, their matching permutation is increasing and hence the identity; their entries are then equal. Thus the coefficient of Delta(X)Delta(Y)K is one when u=v and zero otherwise.")),
            Paragraph(Text("Transport the existing Vandermonde expansion into each set of three variables. Their product has six times six signed monomials. Extract at u=r+(2,1,0), v=q+(2,1,0). Removing the staircase monomial for s leaves the integer margins r(i)-i+s(i). In the nonnegative case these are exactly the natural exponent differences and have total n; the preceding table bijection applies. If a coordinate is negative, the monomial does not divide the extracted exponent and the corresponding table set is empty. No integer-to-natural truncation is used to retain a negative term. The signed contingency sum is therefore the same double coefficient. Decreasing r and q give strictly decreasing u and v, proving the signed Gram delta in every degree.")),
            Paragraph(Text("Combine the self-Gram value one with the actual mixed pairing from the preceding construction. The integral actual Specht character and Theta both have square sum n factorial and have mixed sum n factorial. Their squared difference sums to zero over the integers, so they agree at every permutation. The existing signed-character coefficient comparison then gives the actual same-literal-partition Specht trace equal to HSW.frobChar. The module remains the independently defined polytabloid module; no desired coefficient is installed as its character.")),
            Paragraph(Text("For the full weighted HSW application, this pointwise equality applies to every decreasing even triple r of total 2n and to the rectangle (n,n,0) for every n at least one, including odd n. Replace each coefficient in the two owning weighted expressions by the actual trace. The outer weight is the reciprocal of z_lambda=product k^m_k times m_k factorial. Ev independently replaces each part occurrence a by 2a or by (a,a), retaining duplicate resulting lists; the first expression also has (-1) to the resulting list length. Full cycle lists retain all one-cycles. The weighted coefficient derivation in the owning HemmerStraubWestrem Scribe uses the existing C2 centralizer owner and LatticeHalfFockChargedCoefficients.solution_unique and gives both averages binomial(n/2+2,2) for even n and zero for odd n. The pointwise bridge transports that same derivation to these actual traces; it imposes no bound on n or on the cycle-list length.")),
            Node("cauchy-coefficient-delta", "cauchy_coefficient_delta", "Strict double coefficients of the Cauchy kernel", CauchyStatement(),
                "doubleWeight(u,v) places u on the X variables and v on the Y variables. doubleVandermonde is Delta(X)Delta(Y). cauchyKernel is the product of the nine labelled edge series."),
            Node("signed-gram-delta", "signedContingencyGram_eq_delta", "The finite signed contingency identity", GramStatement(),
                "The total hypothesis is sum(r)=n. The formula also permits a different total for q; when r differs from q the value is zero. Both triples decrease weakly."),
            Node("ordinary-trace", "ordinaryTrace_eq_frobChar", "The actual same-shape ordinary trace formula", TraceStatement(),
                "The hypotheses identify the complete conjugacy partition of g and the complete multiset of tau. tripleShape sorts the three row sizes and deletes only zero parts, retaining equal parts with their multiplicity."),
            Paragraph(Text("To consume the bridge in actual finite character sums, use spechtCharValue: its existing ordinaryTrace theorem certifies the actual trace at the complete cycle partition. Every Ev list has total 2n and positive parts, by induction on the original list. Construct evPartition with exactly that multiset, without sorting away repetitions or dropping one-cycles. The signed even-row sum uses each attached triple in R3(2n), whose total and decreasing hypotheses come directly from its membership. The rectangle sum uses (n,n,0). Apply the class-value bridge term by term in both sums. The existing HSW.result then gives their equality for each partition lambda. Multiplying by the literal reciprocal zPartition(lambda) and summing over lambda gives equality of the two ordinary weighted averages. Their common-value evaluation is the separate coefficient application described above.")),
            Node("classvalue-frobchar", "spechtCharValue_eq_frobChar", "Actual class values and alternant coefficients", ClassStatement(),
                "The class value is the trace of the independently constructed same-literal-shape complex Specht module. The partition rho is the full multiset of tau."),
            Node("ev-consumers", "evSpechtSums_eq_coefficients", "Both actual Ev sums consume the bridge", EvStatement(),
                "signedCoefficientEv and rectangleCoefficientEv abbreviate the two existing inner expressions in HSW.claim, with duplicate list outcomes retained. The signed sum ranges over every attached element of R3(2n)."),
            Node("ordinary-ev", "ordinaryEv_identity", "The original per-partition ordinary Ev identity", EvIdentityStatement(),
                "The two sums are defined using actual spechtCharValue of the complete Ev partitions; n is at least one and lambda is arbitrary."),
            Node("ordinary-weighted-ev", "ordinaryWeightedEv_identity", "Equality of both actual reciprocal-centralizer averages", WeightedStatement(),
                "weightedSignedOrdinaryEv and weightedRectangleOrdinaryEv sum over all partitions lambda of n with reciprocal zPartition(lambda) in the rationals. This equality does not itself evaluate their common value."))));

    private static Formula CauchyStatement() => All("u", Call("NatTriple"), All("v", Call("NatTriple"),
        Imp(Call("strictlyDecreasing", Id("u")), Imp(Call("strictlyDecreasing", Id("v")),
        Eq(Call("doubleKernelCoefficient", Id("u"), Id("v")), Call("kroneckerDelta", Id("u"), Id("v")))))));
    private static Formula GramStatement() => All("n", Nat(), All("r", Call("NatTriple"), All("q", Call("NatTriple"),
        Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")), Imp(Call("decreasing", Id("q")),
        Eq(Call("signedContingencyGram", Id("n"), Id("r"), Id("q")), Call("kroneckerDelta", Id("r"), Id("q")))))))));
    private static Formula TraceStatement() => All("n", Nat(), All("r", Call("NatTriple"), All("rho", Call("Partition", Id("n")),
        All("g", Call("PermFin", Id("n")), All("tau", Call("ListNat"),
        Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")),
        Imp(Call("hasFullConjugacyPartition", Id("g"), Id("rho")), Imp(Call("multisetEqParts", Id("tau"), Id("rho")),
        Eq(Call("ordinarySpechtTrace", Call("tripleShape", Id("r")), Id("g")), Call("complexIntCast", Call("HSWfrobChar", Id("r"), Id("tau")))))))))))));
    private static Formula ClassStatement()
    {
        var equality = Eq(Call("spechtCharValue", Call("tripleShape", Id("r")), Id("rho")), Call("HSWfrobChar", Id("r"), Id("tau")));
        return All("n", Nat(), All("r", Call("NatTriple"), All("rho", Call("Partition", Id("n")), All("tau", Call("ListNat"),
            Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")), Imp(Call("multisetEqParts", Id("tau"), Id("rho")), equality)))))));
    }
    private static Formula EvStatement()
    {
        var first = Eq(Call("signedEvSpechtSum", Id("lambda")), Call("signedCoefficientEv", Id("lambda")));
        var second = Eq(Call("rectangleEvSpechtSum", Id("lambda")), Call("rectangleCoefficientEv", Id("lambda")));
        return All("n", Nat(), All("lambda", Call("Partition", Id("n")), new Formula.Logic(first, FormulaLogicOperator.And, second)));
    }
    private static Formula EvIdentityStatement() => All("n", Nat(), Imp(Call("positive", Id("n")),
        All("lambda", Call("Partition", Id("n")), Eq(Call("signedEvSpechtSum", Id("lambda")), Call("rectangleEvSpechtSum", Id("lambda"))))));
    private static Formula WeightedStatement() => All("n", Nat(), Imp(Call("positive", Id("n")),
        Eq(Call("weightedSignedOrdinaryEv", Id("n")), Call("weightedRectangleOrdinaryEv", Id("n")))));
    private static DocumentBlock Node(string id, string name, string title, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy." + name), H(title),
        StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Nat() => Call("Nat");
}
