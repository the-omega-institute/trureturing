using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class StationaryOccupationResidualCircuitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete last-tail residual vectors and their normalized physical output.",
        H("Stationary Occupation Residual Circuits"),
        Blocks(
            Paragraph(Text(
                "A and K are finite types with decidable equality. Space(K) is the complex "
                + "Euclidean space, and Unitary(A x K) is its physical register unitary group. "
                + "Word(A,n) consists of functions Fin(n) to A. The multiset occ(w) records "
                + "the occupation of w. C(U,n,t,z,w,k) denotes the coefficient (w,k) of the "
                + "actual circuit with the constant schedule U, n slots and starting time t. "
                + "J(blank,n,x) initializes all slots with blank and the memory with x. "
                + "B(blank,x) inserts the memory into one fresh blank slot. "
                + "coefficient(U,v,(i,k)) means the (i,k) coordinate of U(v). "
                + "sector(n,a,w) is the complex inverse square root of multiplicity(n,a) "
                + "when occ(w)=a, and is zero otherwise; multiplicity counts actual occupation words.")),
            Describe.Lean(DescribeId.Create("head-slice"), DeclarationHandle.Create(Prefix + "headSlice"),
                H("Changing only the head count"), StatementSource.FromAuthor(Disp(All("A", Id("Type"), Imp(Alphabet,
                    All("q", A, All("b", Multi, All("h", N, Eq(Call("headSlice", q, b, h),
                        Call("addMultiset", Call("replicate", h, q), Call("filterNotEqual", b, q)))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "filterNotEqual(b,q) retains precisely the letters different from q. Thus the head count is h and every tail count is unchanged. R(q,b) denotes tailCount(q,b); lastTailMass(q,b) is R(q,b) times the occupation multiplicity divided by card(b), in the real numbers."))), DescribeRole.Definition),
            T("head-amplitude", "head_slice_head_amplitude", "Removing one head letter",
                All("A", Id("Type"), Imp(Alphabet, All("q", A, All("b", Multi,
                    All("h", N, Imp(And(Lt(D(0), h), Lt(D(0), Call("R", q, b))),
                        Eq(Mul(Call("sqrtC", Call("headProbability", h, Call("R", q, b))),
                            Call("sqrtC", Mass(h))), Call("sqrtC", Mass(Sub(h, D(1))))))))))),
                "sqrtC is the nonnegative real square root included in the complex numbers. "
                + "The multiplicity erase identity proves this equality, including the "
                + "case R(q,b)=1. Subtraction in the head index is natural subtraction."),
            Describe.Lean(DescribeId.Create("padding-residual"),
                DeclarationHandle.Create(Prefix + "paddingResidual"), H("Residual memory vectors"),
                StatementSource.FromAuthor(Disp(PaddingResidualFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive-tail branch sums over every h in Fin(count(b,q)+1). residualPositiveTail is the bounded tail function i maps to count(b,i), with its nonzero proof; residualHeadIndex embeds h into Fin(count(a,q)+1). The displayed hb and hr bind these proof arguments. The vector is the sink when the tail is empty, and zero outside b<=a. sqrtC includes the nonnegative real square root in the complex numbers; scale denotes complex scalar multiplication."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("physical-residual"), DeclarationHandle.Create(Prefix + "physicalResidual"),
                H("Residuals in physical memory coordinates"), StatementSource.FromAuthor(Disp(All("A", Id("Type"),
                    Imp(And(Alphabet, Call("Nonempty", A)), All("a", Multi, All("b", Multi,
                        Eq(Call("physicalResidual", a, b), Call("coordinateEmbedding", Call("toEmbedding", Call("physicalMemoryEquiv", a)),
                            Call("paddingResidual", Call("maximalHead", a), a, b))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The maximal head has maximum occupation count. physicalMemoryEquiv identifies the padding memory with Fin(d), where d is the product of count(a,i)+1 minus the maximum count. coordinateEmbedding transports the actual residual vector isometrically."))), DescribeRole.Definition),
            Paragraph(Text(
                "Step(a,blank,U,r) means that for every nonzero b<=a and every i:A and k:K, "
                + "the (i,k) coefficient of U(B(blank,r(b))) equals r(erase(b,i))(k) if "
                + "i belongs to b, and equals zero otherwise. Here r maps multisets to "
                + "Space(K). IndicatorEq(c,b,v) means v if c=b and zero otherwise.")),
            T("initial-normalization", "initial_norm_of_sector_output", "The exact output fixes the initial norm",
                General(All("a", Multi, All("blank", A, All("U", Unit,
                    All("x", Space, All("sink", K,
                        Imp(All("w", Word(CardA), All("k", K,
                            Eq(Out(CardA, D(0), x),
                                Mul(Call("sector", CardA, a, w), Call("basis", Id("sink"), k))))),
                            Eq(Call("norm", x), D(1))))))))),
                "The occupation sector has norm one. Embedding it into the sink memory "
                + "preserves that norm, while the actual unitary circuit and initialization "
                + "preserve the norm of x. No initial normalization hypothesis is used."),
            T("concrete-residual-reduction", "target_of_residual_step", "Concrete transitions suffice for attainment",
                All("A", Id("Type"), Imp(And(Alphabet, Call("Nonempty", A)),
                    All("a", Multi, Imp(Call("ResidualStep", a), Call("Target", a))))),
                "ResidualStep is Step for the maximal-capacity head as blank, the fixed "
                + "padding unitary, and physicalResidual(a,-). Target(a) asserts existence "
                + "of one blank, one unitary on A x Fin(d), and unit initial and final memories, "
                + "with every coefficient equal to sector(card(a),a,w) times the final memory; "
                + "d is product(count(a,i)+1) minus the maximum count. The initial memory "
                + "is InvRoot(a) times physicalResidual(a,a), and the terminal memory is "
                + "the sink. The argument also includes the zero multiset."))));

    private static Formula PaddingResidualFormula()
    {
        var value = Call("paddingResidual", q, a, b);
        var count = Call("tailCount", q, b);
        var index = Call("some", Call("pair", Call("residualPositiveTail", q, a, b, Id("hb"), Id("hr")),
            Call("residualHeadIndex", q, a, b, Id("hb"), h)));
        var term = Call("scale", Call("sqrtC", Call("lastTailMass", q, Call("headSlice", q, b, Call("val", h)))), Call("basis", index));
        var sum = Seq(new Formula.Subscript(Sum, Seq(h, Colon, Call("Fin", Call("succ", Call("count", b, q))))), Grp(term));
        var positive = All("hb", Le(b, a), All("hr", Lt(D(0), count), Eq(value, sum)));
        var empty = Imp(And(Le(b, a), Eq(count, D(0))), Eq(value, Call("basis", Call("none"))));
        var outside = Imp(Call("not", Le(b, a)), Eq(value, D(0)));
        return All("A", Id("Type"), Imp(Alphabet, All("q", A, All("a", Multi, All("b", Multi, And(positive, empty, outside))))));
    }

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/StationaryOccupationResidualCircuit.";
    private static DocumentBlock T(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula A => Id("A");
    private static Formula K => Id("K");
    private static Formula a => Id("a");
    private static Formula b => Id("b");
    private static Formula q => Id("q");
    private static Formula h => Id("h");
    private static Formula w => Id("w");
    private static Formula k => Id("k");
    private static Formula x => Id("x");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Multi => Call("Multiset", A);
    private static Formula Space => Call("Space", K);
    private static Formula Unit => Call("Unitary", Call("Prod", A, K));
    private static Formula CardA => Call("card", a);
    private static Formula Alphabet => And(Call("Fintype", A), Call("DecidableEq", A));
    private static Formula Mass(Formula j) => Call("lastTailMass", q, Call("headSlice", q, b, j));
    private static Formula Word(Formula j) => Call("Word", A, j);
    private static Formula Out(Formula slots, Formula time, Formula memory) =>
        Call("C", Id("U"), slots, time, Call("J", Id("blank"), slots, memory), w, k);
    private static Formula General(Formula body) => All("A", Id("Type"), All("K", Id("Type"),
        Imp(And(Alphabet, Call("Fintype", K), Call("DecidableEq", K)), body)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((right, left) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
}
