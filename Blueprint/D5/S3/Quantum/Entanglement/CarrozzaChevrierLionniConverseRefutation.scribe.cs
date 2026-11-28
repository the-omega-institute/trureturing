using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class CarrozzaChevrierLionniConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/CarrozzaChevrierLionniConverseRefutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized four-qubit cluster state is irreducible and has zero ordered and color-averaged readouts at every order at least two.",
        H("A four-qubit counterexample to both converses of the entanglement criterion"),
        Blocks(
            Paragraph(Text(
                "Carrozza, Chevrier and Lionni ask after Corollary 7 of arXiv:2611.27660v1 whether irreducible multipartite entanglement forces strict positivity of the ordered quantity or its color average. Use the cluster state psi with amplitudes 1/2 on 0000, 0011 and 1100, amplitude -1/2 on 1111, and zero elsewhere.")),
            Paragraph(Text(
                "In Definition 1, each normalized factor has a proper party support. A one-dimensional coordinate represents each leg outside the support. The local unitary in a common space can be absorbed into one of the two families of rectangular isometries. At a cut, the grouped maps act on the coefficient matrix by L A R-transpose. Their adjoints recover A, so rank is preserved in both directions.")),
            Paragraph(Text(
                "The rank of a cut matrix for the party-regrouped product is the product of the corresponding factor ranks. Every singleton cut of psi has rank two. The 2-by-2 minor obtained by selecting constant zero and constant one coordinates on each side has diagonal entries 1/2 and -1/2 and off-diagonal entries in {0, 1/2}. Thus every nonempty proper cut has rank at least two. Primality of two assigns each party to exactly one factor of singleton rank two. These effective supports partition the parties and lie inside the proper supports. Stripping the rank-one legs gives rank one for the cut at any nonempty effective support, which contradicts the minor bound.")),
            Paragraph(Text(
                "In Eq. (24), the column is ket-dual and the row is dual-ket. The middle vertex pair reverses the roles of the two strands. For order (a,b,c,d), the entry at ((j',j),(i,i')) sums rho_ab[(i,x),(i',x')] rho_bc[(x',y'),(x,y)] rho_cd[(y,j),(y',j')] over x,x',y,y'. Each rho is a complex partial contraction with conjugation on the bra. Over all 24 permutations the resulting matrix is e e-transpose divided by 16, with e=(1,0,0,1). Its Gram matrix X has trace 1/64 and X squared equals X/64. Induction therefore gives tr(X^n)=(1/64)^n. The ratio in Eq. (30) is one and every summand of Eq. (31) is zero.")),
            Describe.Lean(
                DescribeId.Create("cluster-counterexample"),
                DeclarationHandle.Create(Module + ".cluster_readouts_zero"),
                H("Both readouts vanish at every order"),
                StatementSource.FromAuthor(Disp(WitnessFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem evaluates the general readouts at four parties with local dimension two. The ordered equality ranges over every permutation of the four colors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("both-converses"),
                DeclarationHandle.Create(Module + ".result"),
                H("Both converses fail"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The claim is the disjunction of the two universal assertions for all D at least three, all positive finite local dimensions, every normalized irreducible pure state and all natural orders at least two. The ordered assertion also ranges over all permutations of the colors. Setting D to four, each local dimension to two, and n to two gives a contradiction in each branch."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula WitnessFormula()
    {
        Formula psi = F.Id("clusterState");
        Formula order = F.Id("n");
        Formula sigma = F.Id("sigma");
        Formula orderedZero = Seq(Forall, Sp, sigma, Sp, InMacro, Sp, Apply("Perm", Apply("Fin", D(4))),
            Comma, Sp, Equal(Apply("ordered", psi, sigma, order), D(0)));
        Formula averagedZero = Equal(Apply("averaged", psi, order), D(0));
        Formula allOrders = Seq(Forall, Sp, order, Sp, Geq, Sp, D(2), Comma, Sp,
            And(Seq(Open, orderedZero, Close), averagedZero));
        return allOrders;
    }
}
