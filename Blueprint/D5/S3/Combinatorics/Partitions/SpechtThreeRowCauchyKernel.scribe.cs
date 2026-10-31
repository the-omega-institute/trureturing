using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtThreeRowCauchyKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite Cauchy kernel and signed contingency Gram", H("The finite Cauchy kernel and signed contingency Gram"), Blocks(
            Paragraph(Text("Use six variables Xi,Yj indexed by the disjoint union of two copies of Fin 3. An edge (i,j) has weight k at Xi and k at Yj, with all other exponents zero. Its geometric series has coefficient one exactly at these edge weights. Multiplication by 1-XiYj gives one: the shifted coefficients cancel except at the zero monomial. Define K as the product of these nine labelled series. There is no analytic convergence condition.")),
            Paragraph(Text("The coefficient of K at X^a Y^b, when the natural row margin a has total n, is the cardinality of the existing finite set contingencyTables(n,a,b). Indeed, the product coefficient formula indexes decompositions of the six-variable exponent into nine edge weights. The exponent on edge (i,j) is its table entry A(i,j); the decomposition equation is precisely the three row and three column equations. Sending a decomposition to its Xi coordinate on each edge and sending a table to its nine edge monomials are inverse maps. The total-table equation follows by summing the row margins. Unequal column total gives the empty set automatically.")),
            Paragraph(Text("For any commutative ring and elements xi,yj, let dij=1-xi*yj. The matrix whose i-th row is [di1*di2,di0*di2,di0*di1] has determinant Delta(x)Delta(y), by the three-by-three determinant formula and the polynomial ring identity. If dij*qij=1, scaling row i of q by di0*di1*di2 gives this numerator matrix. The product of the nine d's times the product of the nine q's equals one. It follows that Delta(x)Delta(y) times the product of the qij equals det(q). Applying this to the nine geometric series proves Delta(X)Delta(Y)K=det((1-XiYj) inverse). No character or Schur orthogonality enters this argument.")),
            Paragraph(Text("A term of the determinant selects one edge from each row and column. The coefficient at X^u Y^v in the product of the three selected geometric series is one if u(i)=v(s(i)) for every i and zero otherwise. Its exponent decomposition, when it exists, is unique: the Xi coordinate fixes the exponent on the selected edge. If u and v are strictly decreasing, their matching permutation is increasing and hence the identity; their entries are then equal. Thus the coefficient of Delta(X)Delta(Y)K is one when u=v and zero otherwise.")),
            Paragraph(Text("Transport the existing Vandermonde expansion into each set of three variables. Their product has six times six signed monomials. Extract at u=r+(2,1,0), v=q+(2,1,0). Removing the staircase monomial for s leaves the integer margins r(i)-i+s(i). In the nonnegative case these are exactly the natural exponent differences and have total n; the preceding table bijection applies. If a coordinate is negative, the monomial does not divide the extracted exponent and the corresponding table set is empty. No integer-to-natural truncation is used to retain a negative term. The signed contingency sum is therefore the same double coefficient. Decreasing r and q give strictly decreasing u and v, proving the signed Gram delta in every degree.")),
            Node("cauchy-coefficient-delta", "cauchy_coefficient_delta", "Strict double coefficients of the Cauchy kernel", CauchyStatement(),
                "doubleWeight(u,v) places u on the X variables and v on the Y variables. doubleVandermonde is Delta(X)Delta(Y). cauchyKernel is the product of the nine labelled edge series."),
            Node("signed-gram-delta", "signedContingencyGram_eq_delta", "The finite signed contingency identity", GramStatement(),
                "The total hypothesis is sum(r)=n. The formula also permits a different total for q; when r differs from q the value is zero. Both triples decrease weakly."))));

    private static Formula CauchyStatement() => All("u", Call("NatTriple"), All("v", Call("NatTriple"),
        Imp(Call("strictlyDecreasing", Id("u")), Imp(Call("strictlyDecreasing", Id("v")),
        Eq(Call("doubleKernelCoefficient", Id("u"), Id("v")), Call("kroneckerDelta", Id("u"), Id("v")))))));
    private static Formula GramStatement() => All("n", Nat(), All("r", Call("NatTriple"), All("q", Call("NatTriple"),
        Imp(Call("totalEq", Id("r"), Id("n")), Imp(Call("decreasing", Id("r")), Imp(Call("decreasing", Id("q")),
        Eq(Call("signedContingencyGram", Id("n"), Id("r"), Id("q")), Call("kroneckerDelta", Id("r"), Id("q")))))))));
    private static DocumentBlock Node(string id, string name, string title, Formula statement, string prose) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel." + name), H(title),
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
