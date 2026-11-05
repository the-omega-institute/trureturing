using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaOddParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaOddParity.";
    private static readonly LibraryNoteRef ClassicalSource =
        LibraryNoteRef.Create("D5/L/Fourier/hirschhorngarvanborwein1993cubic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd coefficients of the integral three-core Euler quotient form an exact four-dissection.",
        H("Odd Four-Dissection of the Three-Core Euler Quotient"), Blocks(
            Paragraph(Text("For integer x and y, put Q(x,y)=x^2+x*y+y^2 and C(x,y)=3*Q(x,y)-2*x-y. The finite set CoreFiber(n) consists of all integer pairs with C(x,y)=n. Write E for the integral pentagonal Euler series, so E(q) is the product of 1-q^m over positive integers m. Its constant coefficient is one.")),
            Node("0", "coreOddEquiv", EquivalenceFormula(),
                "For every natural n, the map (x,y) -> (1-2*x,-2*y) is an equivalence from CoreFiber(n) to CoreFiber(4*n+1). It sends C to 4*C+1. Conversely, C(x,y) congruent to one modulo four forces x odd and y even, giving the integer inverse ((1-x)/2,-y/2). No integer pair has C congruent to three modulo four.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(ClassicalSource)),
            Node("1", "integralT", QuotientFormula(),
                "The series integralT lies in the ring of formal power series over the integers. Here expand(3,E) substitutes q^3 for q, and invOfUnit(E,1) is the inverse determined by the unit constant coefficient. Thus integralT(q)=E(q^3)^3/E(q). The rational three-core product theorem identifies each coefficient with the cardinality of CoreFiber(n). Mapping the integral inverse to the rationals preserves that inverse, so the same interpretation applies to integralT.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(ClassicalSource)),
            Node("2", "integralT_coeff_mod_four", CoefficientFormula(),
                "For every natural n, including zero, the coefficient at 4*n+1 equals the coefficient at n, and the coefficient at 4*n+3 vanishes. The fibre equivalence proves the first equality, and the empty residue-three fibres prove the second. The rational coefficient equalities descend to the integers by injectivity of the integer embedding.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(ClassicalSource)),
            Paragraph(Text("Hirschhorn, Garvan and Borwein state the classical four-dissections in identities (1.35) and (1.36), page 676, and prove them in (9.7)-(9.13), pages 689-691. Their normalization is c(q)=3*integralT(q). Identity (1.36) writes c(q) as q*c(q^4) plus a series in q^2, yielding exactly the two odd coefficient equalities above. The even coefficients and the companion b(q) dissection are outside these statements."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("cubic-theta-odd-parity-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            StatementSource.FromAuthor(new Formula.Layout(FormulaLayoutMode.Display, formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Constant(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));

    private static Formula ForEveryN(Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Constant("Nat"), body);

    private static Formula FourNPlus(long residue) => Add(Multiply(Num(4), Id("n")), Num(residue));

    private static Formula EquivalenceFormula() => ForEveryN(new Formula.Relation(
        Call("coreOddEquiv", Id("n")), FormulaRelationOperator.MemberOf,
        Call("Equiv", Call("CoreFiber", Id("n")), Call("CoreFiber", FourNPlus(1)))));

    private static Formula QuotientFormula()
    {
        var euler = Call("pentagonalSeries", new Formula.Integers());
        return new Formula.Logic(
            new Formula.Relation(Constant("integralT"), FormulaRelationOperator.MemberOf,
                Call("PowerSeries", new Formula.Integers())),
            FormulaLogicOperator.And,
            Equal(Constant("integralT"), Multiply(
                new Formula.Power(Call("expand", Num(3), euler), Num(3)),
                Call("invOfUnit", euler, Num(1)))));
    }

    private static Formula CoefficientFormula() => ForEveryN(new Formula.Logic(
        Equal(Call("coeff", FourNPlus(1), Constant("integralT")),
            Call("coeff", Id("n"), Constant("integralT"))),
        FormulaLogicOperator.And,
        Equal(Call("coeff", FourNPlus(3), Constant("integralT")), Num(0))));
}
