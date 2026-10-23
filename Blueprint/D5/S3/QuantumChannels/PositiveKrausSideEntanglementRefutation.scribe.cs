using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class PositiveKrausSideEntanglementRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/PositiveKrausSideEntanglementRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rexiti2022dephasing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two qubit depolarizing channels have strictly positive-definite tetrahedral Kraus operators, yet a Bell-assisted discrimination strategy succeeds with probability 33/56 while every unassisted strategy succeeds with probability at most 47/84.",
        H("Positive Kraus operators with an entanglement advantage"), Blocks(
            Node("unassisted", "successUn", "Unassisted success probability", SuccessFormula(false),
                "For equal prior probabilities, outcome M guesses the first channel and outcome 1-M guesses the second. The Kraus action is the sum of K i times rho times its conjugate transpose. Matrices have complex entries and indices in Fin 2; trace.re is the real part of the trace.",
                AssessedProvenance.FromRepo()),
            Node("assisted", "successAs", "Success probability with a qubit ancilla", SuccessFormula(true),
                "The ancilla is the first factor of Fin 2 × Fin 2. Matrix.kroneckerMap multiplies scalar entries, so the identity acts on the ancilla and each Kraus operator acts on the second factor. Equal priors and the outcome rule agree with successUn.",
                AssessedProvenance.FromRepo()),
            Node("claim", "claim", "The identity polar-factor conjecture", ClaimFormula(),
                "Section 7, printed pages 16–17: \"" + SourceQuote + "\" "
                + "The negative clause is encoded for qubit channels and a qubit ancilla. Strict positive definiteness ensures that the polar unitary is uniquely the identity. Both Kraus families have n operators and right Gram sum equal to the identity. IsDensity is the positive-semidefinite trace-one predicate of SLDSpectralEnergy. Each effect and its complement are positive semidefinite. For every assisted input and effect, the assertion asks for an unassisted input and effect with at least the same success probability. The positive-definite qubit restriction is sufficient for a counterexample to the general negative clause.",
                AssessedProvenance.FromLiterature(Source)),
            Node("refutation", "result", "Refutation by positive tetrahedral Kraus operators", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For a=2 and a=3, use four Kraus operators (aI+sX+tY+uZ)/(2√(a²+3)), with (s,t,u)=(1,1,1),(1,−1,−1),(−1,1,−1),(−1,−1,1). X and Z are the qubit Pauli matrices and Y=Complex.I times XZ. A positive multiple of the identity plus a positive Gram matrix proves strict positive definiteness. The resulting channel sends A to ((a²−1)/(a²+3))A+(2/(a²+3))trace(A)I. Two nonnegative trace pairings bound every unassisted success probability by 47/84. The frozen Bell density is both input and effect for the assisted strategy, whose success probability is 33/56. The strict gap is 5/168. The paper's phase-damping result concerns its particular channel family and is unaffected by this counterexample to the general negative clause.",
                AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rexiti-memarzadeh-mancini-2022-positive-kraus-side-entanglement"),
                    ResolutionKind.Refuted)))));

    private const string SourceQuote = "About the discrimination with side entanglement, it is worth observing the following: i) Side entanglement is very useful for Pauli channels [16]; ii) Side entanglement is partially useful for amplitude damping [6]; iii) Side entanglement is not useful for phase damping channel (present work). Then, we are led to conjecture that side entanglement is useful in channel discrimination if the Kraus operators of the channel admit a polar decomposition with non-trivial unitaries (i.e., not identities). Actually, if the Kraus operators are unitaries, then there is maximal benefit from side entanglement. In contrast, if all Kraus operators have simply the identity as unitary part in the polar decomposition, there is no benefit from side entanglement.";

    private static DocumentBlock Node(string id, string name, string title, Formula formula,
        string prose, AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("rmm-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SuccessFormula(bool assisted)
    {
        Formula n = V("n"), k1 = V("K1"), k2 = V("K2"), rho = V("rho"), m = V("M");
        Formula half = Cast(new Formula.Fraction(D(1), D(2)), Real());
        Formula body = PlusOf(Product(half, TraceReal(Product(m, Action(k1, rho, n, assisted)))),
            Product(half, TraceReal(Product(MinusOf(D(1), m), Action(k2, rho, n, assisted)))));
        return Disp(All("n", Nat(), All("K1", Arrow(Call("Fin", n), MatrixType(false)),
            All("K2", Arrow(Call("Fin", n), MatrixType(false)), All("rho", MatrixType(assisted),
            All("M", MatrixType(assisted), Equal(Call(assisted ? "successAs" : "successUn", k1, k2, rho, m), body)))))));
    }

    private static Formula ClaimFormula() => Disp(Equal(V("claim"), Parenthesized(ClaimBody())));

    private static Formula ClaimBody()
    {
        Formula n = V("n"), k1 = V("K1"), k2 = V("K2"), rho = V("rho"), m = V("M");
        Formula sigma = V("sigma"), effect = V("N");
        Formula conclusion = ExistsIn("sigma", MatrixType(false), ExistsIn("N", MatrixType(false),
            And(Density(sigma), And(Effect(effect), Le(Call("successAs", k1, k2, rho, m),
                Call("successUn", k1, k2, sigma, effect))))));
        Formula strategy = All("rho", MatrixType(true), All("M", MatrixType(true),
            Imp(Density(rho), Imp(Effect(m), conclusion))));
        Formula families = Imp(All("i", Call("Fin", n), Call("PosDef", App(k1, V("i")))),
            Imp(All("i", Call("Fin", n), Call("PosDef", App(k2, V("i")))),
            Imp(Complete(k1, n), Imp(Complete(k2, n), strategy))));
        return All("n", Nat(),
            All("K1", Arrow(Call("Fin", n), MatrixType(false)),
            All("K2", Arrow(Call("Fin", n), MatrixType(false)), families)));
    }

    private static Formula Action(Formula family, Formula state, Formula n, bool assisted)
    {
        Formula k = App(family, V("i"));
        if (assisted)
        {
            Formula multiplication = Lambda("x", Complex(), Lambda("y", Complex(), Product(V("x"), V("y"))));
            k = App(Qualified("Matrix", "kroneckerMap"), multiplication, Cast(D(1), MatrixType(false)), k);
        }
        return SumOver("i", Call("Fin", n), Product(Product(k, state), Call("conjTranspose", k)));
    }
    private static Formula Complete(Formula family, Formula n) => Equal(
        SumOver("i", Call("Fin", n), Product(Call("conjTranspose", App(family, V("i"))), App(family, V("i")))), D(1));
    private static Formula Effect(Formula value) => And(Call("PosSemidef", value), Call("PosSemidef", MinusOf(D(1), value)));
    private static Formula Density(Formula value) => App(Qualified("SLDSpectralEnergy", "IsDensity"), value);
    private static Formula MatrixType(bool assisted)
    {
        Formula index = Call("Fin", D(2));
        if (assisted) index = Parenthesized(Seq(index, Sp, Times, Sp, index));
        return Call("Matrix", index, index, Complex());
    }
    private static Formula TraceReal(Formula value) => Seq(Parenthesized(value), Dot, V("trace"), Dot, V("re"));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula PlusOf(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula MinusOf(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(string name, Formula type, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) => Seq(V("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum, Underscore, Grp(Seq(V(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
