using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.FiniteReadoutFormula;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteAdditiveReadoutBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additive readouts of one coherent source determine quotient blocks and flat marginals.",
        H("Finite Additive Readout Blocks"),
        Blocks(
            Definitions(),
            BlockDefinitions(),
            StateDefinitions(),
            Paragraph(Text(
                "The source G and label spaces A and B are finite additive commutative groups. "
                + "The maps alpha and beta are additive homomorphisms from that same source, "
                + "and the paired map is injective. Blocks are indexed by G modulo the sum of "
                + "the two kernels. Source amplitudes are divided by the square root of the "
                + "source cardinality; labels outside a readout image have zero amplitude.")),
            Describe.Lean(
                DescribeId.Create("finite-readout-paired-block"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.paired_block_iff"),
                H("Paired block criterion"),
                StatementSource.FromAuthor(F.Disp(PairedBlockIff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A pair of readout labels comes from one source element exactly when the two labels "
                    + "occur in the same quotient block. The kernel sum lets representatives on the "
                    + "two sides be joined into one source. This criterion itself requires neither "
                    + "finiteness nor joint injectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-actual-coefficient"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_coefficient_block"),
                H("Actual coefficient blocks"),
                StatementSource.FromAuthor(F.Disp(ActualCoefficientBlock())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a jointly injective pair of readouts, each coefficient of the actual source "
                    + "sum is the normalized indicator of its unique quotient block. The assertion "
                    + "comes from the source sum, rather than a prescribed block matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-right-block-card"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.right_block_card"),
                H("Right block cardinality"),
                StatementSource.FromAuthor(F.Disp(RightBlockCard())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each right block has as many distinct labels as the left readout kernel has "
                    + "elements. Joint injectivity gives the needed bijection."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-source-coset-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.source_coset_product"),
                H("Source cosets and product blocks"),
                StatementSource.FromAuthor(F.Disp(SourceCosetProduct())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The paired readout restricts to a bijection from each source coset onto the "
                    + "product of its left and right label blocks. Both coordinates of the "
                    + "bijection are the original readout values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-actual-block-matrices"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/FiniteAdditiveReadoutBlocks.actual_block_matrices"),
                H("Matrices from the actual source"),
                StatementSource.FromAuthor(F.Disp(ActualBlockMatrices())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Normalized left and right block columns are orthonormal. The actual coefficient "
                    + "matrix factors through these columns with the square-root block weight. "
                    + "Taking its two actual partial traces gives scaled block projections, their "
                    + "column actions, and zero action on the respective conjugate-transpose kernels. "
                    + "Both block projections are Hermitian and idempotent. The blocks on each side "
                    + "are disjoint and their union is precisely that readout's image. Left and right "
                    + "blocks have the respective opposite kernel cardinalities. For every chosen "
                    + "representative, their labels are its readout translated by the opposite kernel "
                    + "image. Both reductions square to the block weight times themselves. Their "
                    + "entries are the same-block indicators summed over the quotient and scaled "
                    + "by the corresponding kernel cardinality divided by the source cardinality. "
                    + "The quotient cardinality is bounded by both ambient label cardinalities."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definitions() => Paragraph(
        Text("Notation is the named Lean definition, not an independent block model. "
            + "Write K = kernelSum(alpha,beta) = alpha.ker sup beta.ker and "
            + "Q = BlockQuotient(alpha,beta) = G / K. "
            + "leftBlock(alpha,beta,q,a) means there is x in G with quotient class q and "
            + "alpha(x) = a; rightBlock uses beta(x) = b. "
            + "actualCoefficient(alpha,beta)(a,b) is the source sum below; "
            + "actualJoint(alpha,beta)(p,r) is actualCoefficient at p times the "
            + "conjugate of actualCoefficient at r. "
            + "actualReducedA and actualReducedB are respectively partialTraceRight and "
            + "partialTraceLeft of actualJoint. leftVectors(alpha,beta)(a,q) and "
            + "rightVectors(alpha,beta)(b,q) "
            + "are the normalized block indicators shown below; blockWeight is real. "
            + "All Fintype.card expressions use the displayed type; complex scalar "
            + "multiplication coerces real weights to complex numbers, and Real.sqrt "
            + "coerces natural cardinalities to reals. The displayed "
            + "a, b, p, r, q are arbitrary elements of A, B, A times B, A times B, Q."));

    private static DocumentBlock BlockDefinitions() => new DocumentBlock.DisplayFormula(And(
            Eq(C("kernelSum", Alpha, Beta),
                C("sup", C("AddMonoidHom.ker", Alpha), C("AddMonoidHom.ker", Beta))),
            Eq(Coeff(Avar, Bvar), Mul(Inv(C("Complex.ofReal", C("Real.sqrt", Card(G)))),
                SumAt("x", G, C("ite", And(Eq(Apply(Alpha, X), Avar),
                    Eq(Apply(Beta, X), Bvar)), One, Zero)))),
            Eq(LeftVectors(Avar, Qvar), Mul(Inv(C("Complex.ofReal", C("Real.sqrt",
                Card(C("AddMonoidHom.ker", Beta))))),
                C("ite", LeftBlock(Qvar, Avar), One, Zero))),
            Eq(RightVectors(Bvar, Qvar), Mul(Inv(C("Complex.ofReal", C("Real.sqrt",
                Card(C("AddMonoidHom.ker", Alpha))))),
                C("ite", RightBlock(Qvar, Bvar), One, Zero))),
            Eq(Weight, Div(Mul(Card(C("AddMonoidHom.ker", Alpha)),
                Card(C("AddMonoidHom.ker", Beta))), Card(G)))));

    private static DocumentBlock StateDefinitions() => new DocumentBlock.DisplayFormula(And(
            Iff(LeftBlock(Qvar, Avar), Ex("x", G, And(
                Eq(C("QuotientAddGroup.mk'", C("kernelSum", Alpha, Beta), X), Qvar),
                Eq(Apply(Alpha, X), Avar)))),
            Iff(RightBlock(Qvar, Bvar), Ex("x", G, And(
                Eq(C("QuotientAddGroup.mk'", C("kernelSum", Alpha, Beta), X), Qvar),
                Eq(Apply(Beta, X), Bvar)))),
            Eq(Entry(C("actualJoint", Alpha, Beta), Id("p"), Id("r")),
                Mul(Coeff(C("Prod.fst", Id("p")), C("Prod.snd", Id("p"))),
                    C("star", Coeff(C("Prod.fst", Id("r")), C("Prod.snd", Id("r")))))),
            Eq(C("actualSourceKet", Alpha, Beta),
                Smul(Inv(C("Complex.ofReal", C("Real.sqrt", Card(G)))),
                    SumAt("x", G, C("Pi.single", C("Prod.mk", Apply(Alpha, X),
                        Apply(Beta, X)), One)))),
            Eq(ReducedA, C("partialTraceRight", C("actualJoint", Alpha, Beta))),
            Eq(ReducedB, C("partialTraceLeft", C("actualJoint", Alpha, Beta)))));

    private static Formula PairedBlockIff() => Theorem(
        All("a", A, All("b", B,
            Iff(Ex("x", G, And(Eq(Apply(Alpha, X), Avar), Eq(Apply(Beta, X), Bvar))),
                Ex("q", Q, And(LeftBlock(Qvar, Avar), RightBlock(Qvar, Bvar)))))),
        paired: false);

    private static Formula ActualCoefficientBlock() => Theorem(
        All("a", A, All("b", B,
            Eq(Coeff(Avar, Bvar), Mul(Inv(C("Complex.ofReal", C("Real.sqrt", Card(G)))),
                SumAt("q", Q, C("ite", And(LeftBlock(Qvar, Avar),
                    RightBlock(Qvar, Bvar)), One, Zero)))))), paired: true);

    private static Formula RightBlockCard() => Theorem(
        All("q", Q, Eq(FilterCard(B, "b", RightBlock(Qvar, Bvar)),
            Card(C("AddMonoidHom.ker", Alpha)))), paired: true);

    private static Formula SourceCosetProduct()
    {
        Formula sourceCoset = C("Subtype", Lambda("x", G, Eq(C("QuotientAddGroup.mk'",
            C("kernelSum", Alpha, Beta), X), Qvar)));
        Formula left = C("Subtype", Lambda("a", A, LeftBlock(Qvar, Avar)));
        Formula right = C("Subtype", Lambda("b", B, RightBlock(Qvar, Bvar)));
        Formula equiv = C("Equiv", sourceCoset, C("Prod", left, right));
        return Theorem(All("q", Q,
            Ex("e", equiv, All("x", sourceCoset,
                And(Eq(C("Prod.fst", C("Prod.fst", Apply(Id("e"), X))),
                        Apply(Alpha, C("Subtype.val", X))),
                    Eq(C("Prod.fst", C("Prod.snd", Apply(Id("e"), X))),
                        Apply(Beta, C("Subtype.val", X))))))), paired: true);
    }

    private static Formula ActualBlockMatrices()
    {
        Formula u = LeftMatrix;
        Formula v = RightMatrix;
        Formula pa = MatMul(u, Adj(u));
        Formula pb = MatMul(v, Adj(v));
        return Theorem(And(
            Eq(MatMul(Adj(u), u), One),
            Eq(MatMul(Adj(v), v), One),
            Eq(CoefficientMatrix, Smul(C("Complex.ofReal", C("Real.sqrt", Weight)),
                MatMul(u, Adj(v)))),
            Eq(ReducedA, Smul(Weight, pa)),
            Eq(ReducedB, Smul(Weight, pb)),
            All("q", Q, Eq(MulVec(ReducedA, Col(u, Qvar)), Smul(Weight, Col(u, Qvar)))),
            All("q", Q, Eq(MulVec(ReducedB, Col(v, Qvar)), Smul(Weight, Col(v, Qvar)))),
            All("v", new Formula.TypeArrow(A, Complex),
                Imp(Eq(MulVec(Adj(u), Id("v")), Zero),
                    Eq(MulVec(ReducedA, Id("v")), Zero))),
            All("v", new Formula.TypeArrow(B, Complex),
                Imp(Eq(MulVec(Adj(v), Id("v")), Zero),
                    Eq(MulVec(ReducedB, Id("v")), Zero))),
            Eq(MatMul(pa, pa), pa), C("Matrix.IsHermitian", pa),
            Eq(MatMul(pb, pb), pb), C("Matrix.IsHermitian", pb),
            And(
                All("a", A, All("q", Q, All("r", Q,
                    Imp(And(LeftBlock(Qvar, Avar), LeftBlock(Id("r"), Avar)),
                        Eq(Qvar, Id("r")))))),
                All("b", B, All("q", Q, All("r", Q,
                    Imp(And(RightBlock(Qvar, Bvar), RightBlock(Id("r"), Bvar)),
                        Eq(Qvar, Id("r")))))),
                All("a", A, Iff(Ex("q", Q, LeftBlock(Qvar, Avar)),
                    Member(Avar, C("Set.range", Alpha)))),
                All("b", B, Iff(Ex("q", Q, RightBlock(Qvar, Bvar)),
                    Member(Bvar, C("Set.range", Beta))))),
            All("q", Q, Eq(FilterCard(A, "a", LeftBlock(Qvar, Avar)),
                Card(C("AddMonoidHom.ker", Beta)))),
            All("q", Q, Eq(FilterCard(B, "b", RightBlock(Qvar, Bvar)),
                Card(C("AddMonoidHom.ker", Alpha)))),
            All("x", G, All("a", A,
                Iff(LeftBlock(C("QuotientAddGroup.mk'", C("kernelSum", Alpha, Beta), X),
                        Avar),
                    Ex("t", C("AddMonoidHom.ker", Beta),
                        Eq(Avar, FiniteReadoutFormula.Add(Apply(Alpha, X),
                            Apply(Alpha, C("Subtype.val", Id("t"))))))))),
            All("x", G, All("b", B,
                Iff(RightBlock(C("QuotientAddGroup.mk'", C("kernelSum", Alpha, Beta), X),
                        Bvar),
                    Ex("s", C("AddMonoidHom.ker", Alpha),
                        Eq(Bvar, FiniteReadoutFormula.Add(Apply(Beta, X),
                            Apply(Beta, C("Subtype.val", Id("s"))))))))),
            Eq(MatMul(ReducedA, ReducedA), Smul(Weight, ReducedA)),
            Eq(MatMul(ReducedB, ReducedB), Smul(Weight, ReducedB)),
            All("a", A, All("c", A,
                Eq(Entry(ReducedA, Avar, Id("c")),
                    Mul(Div(Card(C("AddMonoidHom.ker", Alpha)), Card(G)),
                        SumAt("q", Q, C("ite", And(LeftBlock(Qvar, Avar),
                            LeftBlock(Qvar, Id("c"))), One, Zero)))))),
            All("b", B, All("d", B,
                Eq(Entry(ReducedB, Bvar, Id("d")),
                    Mul(Div(Card(C("AddMonoidHom.ker", Beta)), Card(G)),
                        SumAt("q", Q, C("ite", And(RightBlock(Qvar, Bvar),
                            RightBlock(Qvar, Id("d"))), One, Zero)))))),
            Le(Card(Q), C("min", Card(A), Card(B)))), paired: true);
    }

    private static Formula Id(string name) => F.Id(name);
}

internal static class FiniteReadoutFormula
{
    internal static Formula Id(string name) => F.Id(name);
    internal static Formula C(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        Formula[] dotted = parts.SelectMany((part, index) =>
            index == 0 ? new Formula[] { OperatorPart(part) } : [F.Dot, OperatorPart(part)]).ToArray();
        return new Formula.Apply(F.Seq(F.Operatorname, F.Grp(dotted)), [.. args]);
    }
    private static Formula OperatorPart(string part) => part.EndsWith('\'')
        ? F.Seq(Id(part[..^1]), F.Apos)
        : Id(part);
    internal static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    internal static Formula Lambda(string name, Formula type, Formula body) =>
        F.Seq(F.Lambda, F.Sp, Id(name), F.Sp, F.InMacro, F.Sp, type,
            F.Comma, F.Sp, body);
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula And(params Formula[] parts) => parts.Reverse().Aggregate((tail, head) => new Formula.Logic(head, FormulaLogicOperator.And, tail));
    internal static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    internal static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    internal static Formula Inv(Formula a) => new Formula.Power(a, new Formula.Negate(One));
    internal static Formula Smul(Formula a, Formula b) => C("SMul.smul", a, b);
    internal static Formula MatMul(Formula a, Formula b) => Mul(a, b);
    internal static Formula Adj(Formula a) => C("Matrix.conjTranspose", a);
    internal static Formula MulVec(Formula a, Formula b) => C("Matrix.mulVec", a, b);
    internal static Formula Col(Formula a, Formula q) => C("Matrix.col", a, q);
    internal static Formula Entry(Formula m, Formula a, Formula b) => Apply(m, a, b);
    internal static Formula Card(Formula t) => C("Fintype.card", t);
    internal static Formula NatCard(Formula t) => C("Nat.card", t);
    internal static Formula SumAt(string name, Formula type, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(Id(name), F.Sp, F.InMacro, F.Sp, type)), F.Grp(body));
    internal static Formula FilterCard(Formula type, string name, Formula condition) =>
        C("Finset.card", C("Finset.filter", C("Finset.univ", type),
            Lambda(name, type, condition)));

    internal static Formula G => Id("G");
    internal static Formula A => Id("A");
    internal static Formula B => Id("B");
    internal static Formula Alpha => Id("alpha");
    internal static Formula Beta => Id("beta");
    internal static Formula X => Id("x");
    internal static Formula Avar => Id("a");
    internal static Formula Bvar => Id("b");
    internal static Formula Qvar => Id("q");
    internal static Formula One => F.D(1);
    internal static Formula Zero => F.D(0);
    internal static Formula Complex => F.Seq(F.Mathbb, F.Grp(Id("C")));
    internal static Formula Q => C("BlockQuotient", Alpha, Beta);
    internal static Formula Weight => C("blockWeight", Alpha, Beta);
    internal static Formula CoefficientMatrix => C("actualCoefficient", Alpha, Beta);
    internal static Formula ReducedA => C("actualReducedA", Alpha, Beta);
    internal static Formula ReducedB => C("actualReducedB", Alpha, Beta);
    internal static Formula LeftMatrix => C("leftVectors", Alpha, Beta);
    internal static Formula RightMatrix => C("rightVectors", Alpha, Beta);
    internal static Formula Coeff(Formula a, Formula b) => Entry(CoefficientMatrix, a, b);
    internal static Formula LeftBlock(Formula q, Formula a) => C("leftBlock", Alpha, Beta, q, a);
    internal static Formula RightBlock(Formula q, Formula b) => C("rightBlock", Alpha, Beta, q, b);
    internal static Formula LeftVectors(Formula a, Formula q) => Entry(LeftMatrix, a, q);
    internal static Formula RightVectors(Formula b, Formula q) => Entry(RightMatrix, b, q);

    internal static Formula Theorem(Formula body, bool paired)
    {
        Formula readouts = All("alpha", C("AddMonoidHom", G, A),
            All("beta", C("AddMonoidHom", G, B),
                paired ? Imp(C("Function.Injective",
                    Lambda("x", G, C("Prod.mk", Apply(Alpha, X), Apply(Beta, X)))), body) : body));
        Formula instances = paired
            ? All("fG", C("Fintype", G), All("fA", C("Fintype", A),
                All("fB", C("Fintype", B), All("dG", C("DecidableEq", G),
                    All("dA", C("DecidableEq", A),
                        All("dB", C("DecidableEq", B), readouts))))))
            : readouts;
        Formula universe = F.Seq(Id("Type"), F.Star);
        return All("G", universe, All("A", universe,
            All("B", universe,
                All("gG", C("AddCommGroup", G),
                    All("gA", C("AddCommGroup", A),
                        All("gB", C("AddCommGroup", B), instances))))));
    }
}
