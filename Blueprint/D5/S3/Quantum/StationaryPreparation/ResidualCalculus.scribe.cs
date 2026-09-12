using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class ResidualCalculusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local residual transitions determine all coefficients of a fixed-unitary circuit.",
        H("Last-Tail Mass and Circuit Residuals"),
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
            Describe.Lean(DescribeId.Create("last-tail-mass"),
                DeclarationHandle.Create(Prefix + "lastTailMass"), H("Last-tail multiplicity"),
                StatementSource.FromAuthor(Disp(All("A", Id("Type"), Imp(Alphabet,
                    All("q", A, All("b", Multi, Eq(Call("lastTailMass", q, b),
                        Call("divideR", Mul(Call("castR", Call("tailCount", q, b)),
                            Call("castR", Call("multiplicity", Call("card", b), b))), Call("castR", Call("card", b)))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "tailCount(q,b), also written R(q,b), sums the counts of letters other than q. multiplicity(n,b) counts occupation-b words of length n. castR is the natural-number inclusion into the reals and divideR is real division, including division by zero. Last-tail multiplicity is therefore defined for every b."))), DescribeRole.Definition),
            Paragraph(Text(
                "Step(a,blank,U,r) means that for every nonzero b<=a and every i:A and k:K, "
                + "the (i,k) coefficient of U(B(blank,r(b))) equals r(erase(b,i))(k) if "
                + "i belongs to b, and equals zero otherwise. Here r maps multisets to "
                + "Space(K). IndicatorEq(c,b,v) means v if c=b and zero otherwise.")),
            T("all-circuit-coefficients", "circuit_output_of_residuals", "Local residual equations determine the output",
                General(All("blank", A, All("U", Unit, All("a", Multi,
                    All("r", Call("Function", Multi, Space), All("f", Space,
                        Imp(And(Eq(Call("r", D(0)), f), Step),
                            All("n", N, All("t", N, All("b", Multi,
                                Imp(And(Eq(Call("card", b), n), Le(b, a)),
                                    All("w", Word(n), All("k", K,
                                        Eq(Out(n, t, Call("r", b)),
                                            Call("IndicatorEq", Call("occ", w), b, Call("f", k)))))))))))))))),
                "Induction on the number of slots uses the actual circuit recursion. "
                + "A legal first letter erases one occurrence from the remaining multiset; "
                + "an absent first letter makes the coefficient zero. The empty word "
                + "uses r(0)=f. This includes all legal and illegal words."),
            T("normalized-coefficients", "normalized_output_of_residuals", "Normalized equal-phase occupation output",
                General(All("blank", A, All("U", Unit, All("a", Multi,
                    All("r", Call("Function", Multi, Space), All("f", Space,
                        Imp(And(Eq(Call("r", D(0)), f), Step), All("w", Word(CardA),
                            All("k", K, Eq(Out(CardA, D(0), Call("scale", InvRoot, Call("r", a))),
                                Mul(Call("sector", CardA, a, w), Call("f", k)))))))))))),
                "InvRoot(a) is the complex inverse of the square root of M(card(a),a). "
                + "The sector coefficient is this same positive real amplitude on words "
                + "of occupation a and zero on every other word. Linearity transfers "
                + "the unnormalized coefficient identity to the scaled input."))));

    private const string Prefix = "D5/S3/Quantum/StationaryPreparation/ResidualCalculus.";
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
    private static Formula n => Id("n");
    private static Formula t => Id("t");
    private static Formula w => Id("w");
    private static Formula k => Id("k");
    private static Formula f => Id("f");
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Multi => Call("Multiset", A);
    private static Formula Space => Call("Space", K);
    private static Formula Unit => Call("Unitary", Call("Prod", A, K));
    private static Formula CardA => Call("card", a);
    private static Formula InvRoot => Call("inverse", Call("sqrtC", Call("multiplicity", CardA, a)));
    private static Formula Alphabet => And(Call("Fintype", A), Call("DecidableEq", A));
    private static Formula Step => All("b", Multi,
        Imp(And(Le(b, a), new Formula.Relation(b, FormulaRelationOperator.NotEqual, D(0))),
            All("i", A, All("k", K,
                Eq(Call("coefficient", Id("U"), Call("blankMemory", Id("blank"), Call("r", b)), Call("pair", Id("i"), k)),
                    Call("if", new Formula.Relation(Id("i"), FormulaRelationOperator.MemberOf, b),
                        Call("r", Call("erase", b, Id("i")), k), D(0)))))));
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
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] terms) => terms.Reverse().Aggregate((right, left) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

}
