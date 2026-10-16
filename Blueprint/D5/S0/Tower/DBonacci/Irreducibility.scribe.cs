using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciIrreducibilityDocument : IScribeDocumentDefinition
{
    private static Formula Q => Id("q");
    private static Formula Z => Id("z");
    private static Formula Beta => Call("ofReal", Call("dbonacciPerronRoot", Q));
    private static Formula Polynomial(string ring) => Subtract(
        Call("pow", Call("X", Id(ring)), Q),
        Call("sumPowersBelow", Call("X", Id(ring)), Q));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula ForOrders(Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("q"), Id("N"),
        Imp(new Formula.Relation(Num(2), FormulaRelationOperator.LessThanOrEqual, Q), body));
    private static Formula RootLocation => ForOrders(new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create("z"), Id("C"),
        Imp(Call("IsRoot", Polynomial("C"), Z), new Formula.Logic(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThanOrEqual, Call("norm", Z)),
            FormulaLogicOperator.Iff, Equal(Z, Beta)))));
    private static Formula SimpleRoot => ForOrders(And(
        Call("IsRoot", Polynomial("C"), Beta),
        NotEqual(Call("eval", Call("derivative", Polynomial("C")), Beta), Num(0))));
    private static Formula Irreducibility => ForOrders(And(
        Call("Irreducible", Polynomial("Z")), Call("Irreducible", Polynomial("Q"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multinacci polynomial has a single simple root outside the open unit disc and is irreducible.",
        H("Multinacci root location and irreducibility"),
        Blocks(
            Paragraph(Text("For every integer order q>=2, use the literal polynomial "
                + "X^q-sum(i<q)X^i and the existing dbonacciPerronRoot(q) in (1,2). "
                + "In the formulas, X(R) is the indeterminate over R and sumPowersBelow(X,q) is "
                + "the finite sum of X^i over i<q; N,Z,Q,C denote the natural, integer, rational "
                + "and complex number systems. This is a classical multinacci result associated with Alfred Brauer's paper "
                + "On algebraic equations with all but one root in the interior of the unit circle, "
                + "Mathematische Nachrichten 4, 250-257, DOI 10.1002/mana.3210040123. "
                + "The proof here is independent of that paper's theorem text.")),
            Describe.Lean(
                DescribeId.Create("multinacci-complex-root-location"),
                DeclarationHandle.Create("D5/S0/Tower/DBonacci/Irreducibility.dbonacci_complex_root_location"),
                H("Exact complex root location"),
                StatementSource.FromAuthor(RootLocation),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ArithUnits/brauer1950roots")),
                Blocks(Paragraph(Text("For any complex root z with radius r>=1, the triangle "
                    + "inequality and the strictly decreasing reciprocal sum give r<=beta. "
                    + "The geometric-sum identity gives z^q(2-z)=1. Equality at r=1 forces z=1, "
                    + "contradicting q>=2. If 1<r<beta, the reciprocal inequality and geometric "
                    + "sum give r^q(2-r)>1, contrary to the reverse triangle inequality. Thus "
                    + "r=beta, and equality in that inequality forces z=r. The converse uses beta>1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("multinacci-simple-perron-root"),
                DeclarationHandle.Create("D5/S0/Tower/DBonacci/Irreducibility.dbonacciPerronRoot_simple"),
                H("The Perron root is simple"),
                StatementSource.FromAuthor(SimpleRoot),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ArithUnits/brauer1950roots")),
                Blocks(Paragraph(Text("Euler's identity at a root gives beta*f'(beta)="
                    + "sum(i<q)(q-i)beta^i. Every summand is nonnegative and the term i=0 is "
                    + "strictly positive. The formal derivative is therefore nonzero, without "
                    + "assuming irreducibility or squarefreeness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("multinacci-integer-rational-irreducibility"),
                DeclarationHandle.Create("D5/S0/Tower/DBonacci/Irreducibility.dbonacci_irreducible"),
                H("Integer and rational irreducibility"),
                StatementSource.FromAuthor(Irreducibility),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ArithUnits/brauer1950roots")),
                Blocks(Paragraph(Text("A monic integer factorization has nonzero factor constants "
                    + "because their product is -1. Exactly one factor can vanish at beta: if "
                    + "both did, the product derivative would vanish. Every root of the other "
                    + "factor lies strictly inside the unit circle. If this complementary factor "
                    + "were nonconstant, its full complex root multiset, with multiplicities, "
                    + "would have product of norms below one. The monic constant-product formula "
                    + "would make its nonzero integer constant have absolute value below one, "
                    + "a contradiction. The complementary factor is one in either factor case. "
                    + "Monicity supplies primitivity, and Gauss's lemma transfers to Q. "
                    + "This irreducibility makes the actual integral Plus evaluation at beta "
                    + "faithful, which detects original finite-order scalar actions."))),
                DescribeRole.Theorem))));
}
