using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class PetrTurekWreathEigenvaluesRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/petrturek2025wreath");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The wreath eigenvalues indexed by three and five coincide at fourteen and five.",
        H("A repeated value among the wreath eigenvalues"),
        Blocks(
            Paragraph(Text("Petr and Turek's Theorem 1.5 identifies explicit formulas with the eigenvalues of the wreath matrix. The rational formulas below retain the paper's indices. Their equality at n = 14 and k = 5 answers Question 5.5 negatively. The identification with the matrix spectrum is a result of the cited paper; the Lean proof establishes the arithmetic refutation of distinctness.")),
            Node("lambda-one", "The first eigenvalue formula", "lambdaOne", LambdaOneFormula(),
                "Theorem 1.5, page 3, states: “The value of λ₁ is n(n−k)!k!/(2g(g!)ⁿ⁄ᵍ) if k ∤ n and n²(n−k)!/(k²(k!)ⁿ⁄ᵏ⁻¹(n/k)!) if k ∣ n.” Here g = gcd(n,k). The arguments n and k are natural numbers and the values are rational. Nat.div denotes natural-number division, and subtraction within a natural-number argument is truncated subtraction. Every conversion from Nat to Rat is displayed by a type annotation."),
            Node("lam", "The indexed eigenvalue formula", "lam", LamFormula(),
                "Theorem 1.5, page 3, states: “If g = 1, for 2 ≤ l ≤ k we moreover have” λₗ = (−1)ˡ ½ l! k! (n−k−l)! (n−2k−1) C(k,l) − ½ k! (n−k)! + l! C(k+1,l+1) ∑ⱼ₌₀ˡ (−1)ˡ⁻ʲ (k−j)! (n−k−l+j)!. The value at l = 1 is lambdaOne n k. The sum over Finset.range (l+1) contains j = 0 through l once each. The factor n−2k−1 is evaluated in Rat; factorial arguments and the exponent l−j are evaluated in Nat. Outside the positive coprime range 2k < n and 1 ≤ l ≤ k, these total formulas assert no spectral interpretation."),
            Node("claim", "Distinctness in the coprime range", "claim",
                Eqn(Call("claim"), Parenthesized(ClaimBody())),
                "Question 5.5, page 16, asks verbatim: “Are the eigenvalues λ₁, λ₂, …, λₖ from Theorem 1.5 all distinct?” The proposition expresses an affirmative answer restricted to coprime positive parameters with 2k < n. The indices l and lprime (Lean's l') range over Finset.Icc 1 k. An affirmative answer to the source question implies this restricted proposition.",
                AssessedProvenance.FromRepo(Source)),
            Node("result", "Refutation by two coincident formula values", "result",
                new Formula.Not(Parenthesized(ClaimBody())),
                "At n = 14 and k = 5, the indices 3 and 5 are distinct and both lie in Finset.Icc 1 5. The parameters satisfy 0 < 5, 2·5 < 14 and Nat.Coprime 14 5. Normalizing the two rational expressions gives lam 14 5 3 = 17107200 and lam 14 5 5 = 17107200, contradicting the displayed distinctness proposition. Theorem 1.5 expressly permits repeated values and adds their multiplicities, so its statement remains intact.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("petr-turek-2025-wreath-eigenvalue-coincidence"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, AssessedProvenance? provenance = null, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ptw-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => StrataLint.Scribe.FormulaDsl.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Rat() => new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Rat()));
    private static Formula Fac(Formula value) => QCall("Nat", "factorial", value);
    private static Formula RFac(Formula value) => Cast(Fac(value));
    private static Formula Div(Formula left, Formula right) => QCall("Nat", "div", left, right);
    private static Formula GcdValue() => QCall("Nat", "gcd", V("n"), V("k"));

    private static Formula LambdaOneFormula()
    {
        Formula n = V("n"), k = V("k");
        Formula divisible = Seq(k, Sp, Mid, Sp, n);
        Formula yes = new Formula.Fraction(Mul(Pow(Cast(n), D(2)), RFac(Sub(n, k))),
            Mul(Mul(Pow(Cast(k), D(2)), Pow(RFac(k), Sub(Div(n, k), D(1)))), RFac(Div(n, k))));
        Formula no = new Formula.Fraction(Mul(Mul(Cast(n), RFac(Sub(n, k))), RFac(k)),
            Mul(Mul(D(2), Cast(GcdValue())), Pow(RFac(GcdValue()), Div(n, GcdValue()))));
        return All("n", Nat(), All("k", Nat(), Eqn(Call("lambdaOne", n, k),
            Call("ite", divisible, yes, no))));
    }

    private static Formula LamFormula()
    {
        Formula n = V("n"), k = V("k"), l = V("l"), j = V("j");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula first = Mul(Mul(Mul(Mul(Mul(Mul(Pow(new Formula.Negate(D(1)), l), half),
            RFac(l)), RFac(k)), RFac(Sub(Sub(n, k), l))), Sub(Sub(Cast(n), Mul(D(2), Cast(k))), D(1))),
            Cast(QCall("Nat", "choose", k, l)));
        Formula second = Mul(Mul(half, RFac(k)), RFac(Sub(n, k)));
        Formula summand = Mul(Mul(Pow(new Formula.Negate(D(1)), Sub(l, j)), RFac(Sub(k, j))),
            RFac(Add(Sub(Sub(n, k), l), j)));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Member(j, QCall("Finset", "range", Add(l, D(1))))), Sp, Parenthesized(summand));
        Formula third = Mul(Mul(RFac(l), Cast(QCall("Nat", "choose", Add(k, D(1)), Add(l, D(1))))), sum);
        return All("n", Nat(), All("k", Nat(), All("l", Nat(), Eqn(Call("lam", n, k, l),
            Call("ite", Eqn(l, D(1)), Call("lambdaOne", n, k), Add(Sub(first, second), third))))));
    }

    private static Formula ClaimBody()
    {
        Formula n = V("n"), k = V("k"), l = V("l"), r = V("lprime");
        Formula indices = QCall("Finset", "Icc", D(1), k);
        return All("n", Nat(), All("k", Nat(), Imp(Less(D(0), k), Imp(Less(Mul(D(2), k), n),
            Imp(QCall("Nat", "Coprime", n, k), All("l", Nat(), Imp(Member(l, indices),
                All("lprime", Nat(), Imp(Member(r, indices), Imp(Ne(l, r),
                    Ne(Call("lam", n, k, l), Call("lam", n, k, r))))))))))));
    }
}
