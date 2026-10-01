using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class PurityTimeReversalOverlapMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/serranoensastiga2026monogamy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every bipartition of N qubits into a part A of k qubits and its non-empty complement, the minimum over pure states of the purity of the reduced state plus its overlap with the time-reversed reduced state is 2^(k-N) when 2k > N and 2^(1-k) when 2k <= N. This proves Conjecture 2 of E. Serrano-Ensastiga, O. Giraud and J. Martin (arXiv:2507.12680), who proved the case k = 1 and found the other values numerically for up to ten qubits.",
        H("The minimum of purity plus time-reversal overlap"),
        Blocks(
            Node("reduced", "The reduced state", ReducedFormula(),
                "For a set A of qubits among N and a vector psi of amplitudes on the configurations of the N qubits, the reduced state rho_A is the partial trace over the qubits outside A of the outer product of psi with itself, written on pairs (x, z) of configurations of A and of the other qubits: its entry at x, y is the sum over z of psi(x, z) times the complex conjugate of psi(y, z).",
                "reducedState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("time-reversed", "The time-reversed state", TimeReversedFormula(),
                "With sigma_y = i X Z for the qubit Pauli matrices X and Z, and Y the k-fold tensor power of sigma_y on the qubits of A, whose entry at configurations x, y of A is the product over the qubits i of A of sigma_y(x_i, y_i), the time-reversed matrix of rho is Y times the entrywise complex conjugate of rho times Y.",
                "timeReversed", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("quantity", "Purity plus overlap", QuantityFormula(),
                "F_A(psi) is the real part of Tr(rho_A rho_A) + Tr(rho_A rho~_A), the sum of the purity of rho_A and the overlap R of rho_A with its time-reversed matrix.",
                "purityPlusOverlap", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("min-value", "The conjectured minimum", MinValueFormula(),
                "m(N, k) is 2^k / 2^N when N < 2k and 2 / 2^k otherwise.",
                "conjecturedMin", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 2", ClaimFormula(),
                "For every N and every set A of qubits among N with 1 <= |A| < N: every unit vector psi gives F_A(psi) >= m(N, |A|), and some unit vector attains equality.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Write d = 2^k and r = 2^(N-k), let M be the d x r matrix of amplitudes psi(x, z), so that rho_A = M M^H with trace 1, and let Phi = Y conj(M). The matrix Y is Hermitian and Y Y = 1, so the time-reversed matrix of rho_A is Phi Phi^H, its trace is 1, and Phi^H Phi is the entrywise conjugate of M^H M. First, Tr(rho_A rho~_A) = Tr((M^H Phi)(M^H Phi)^H) >= 0, and Tr(rho_A^2) = Tr((M^H M)^2) is the squared Frobenius norm of the r x r matrix M^H M, which is at least |Tr(M^H M)|^2 / r = 1/r by the Cauchy-Schwarz inequality on its diagonal. Second, for the Hermitian matrix S = rho_A + rho~_A the real part of Tr(S^2) equals 2 F_A(psi), and it is the squared Frobenius norm of S, which is at least |Tr S|^2 / d = 4/d. So F_A(psi) >= max(1/r, 2/d), which is m(N, k). If 2k <= N, choose an injection iota of A into the other qubits and let psi(x, z) = d^(-1/2) when z extends x along iota by zeros, and 0 otherwise; then rho_A and its time-reversed matrix are both the identity divided by d, and F_A(psi) = 2/d. If 2k > N, choose an injection kappa of the other qubits into A and a qubit i0 of A outside its image, and let psi(x, z) = r^(-1/2) when x extends z along kappa by zeros, and 0 otherwise; then M^H M is the identity divided by r, so Tr(rho_A^2) = 1/r, and every entry of M^H Phi contains the factor sigma_y(0, 0) = 0 at the qubit i0, so the overlap vanishes and F_A(psi) = 1/r.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("serrano-ensastiga-2026-purity-time-reversal-overlap-minimum"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("overlap-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula SomeIn(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula States() => Seq(Complexes(), Caret, Grp(F.Id("Conf")));
    private static Formula Card(Formula set) => new Formula.Absolute(set);
    private static Formula Rho() => Call(F.Id("reducedState"), F.Id("A"), F.Id("psi"));
    private static Formula Tr(Formula value) => Call(F.Id("Tr"), value);

    private static Formula ReducedFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), psi = F.Id("psi");
        Formula entry = Call(F.Id("reducedState"), F.Id("A"), psi, x, y);
        Formula sum = Seq(F.Sum, Underscore, Grp(z), Sp,
            Mul(new Formula.Apply(psi, [x, z]), Call(F.Id("conj"), new Formula.Apply(psi, [y, z]))));
        return Disp(Equal(entry, sum));
    }

    private static Formula TimeReversedFormula()
    {
        Formula rho = F.Id("rho"), y = F.Id("Y");
        return Disp(Equal(Call(F.Id("timeReversed"), F.Id("A"), rho),
            Mul(Mul(y, Call(F.Id("conj"), rho)), y)));
    }

    private static Formula QuantityFormula()
    {
        Formula rho = Rho();
        Formula sum = Add(Tr(Mul(rho, rho)), Tr(Mul(rho, Call(F.Id("timeReversed"), F.Id("A"), rho))));
        return Disp(Equal(Call(F.Id("purityPlusOverlap"), F.Id("A"), F.Id("psi")), Call(F.Id("Re"), sum)));
    }

    private static Formula MinValueFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k");
        Formula value = Call(F.Id("ite"), Rel(n, FormulaRelationOperator.LessThan, Mul(D(2), k)),
            new Formula.Fraction(new Formula.Power(D(2), k), new Formula.Power(D(2), n)),
            new Formula.Fraction(D(2), new Formula.Power(D(2), k)));
        return Disp(Equal(Call(F.Id("conjecturedMin"), n, k), value));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), a = F.Id("A"), psi = F.Id("psi");
        Formula unit = Equal(Seq(F.Sum, Underscore, Grp(F.Id("w")), Sp,
            new Formula.Power(new Formula.Absolute(new Formula.Apply(psi, [F.Id("w")])), D(2))), D(1));
        Formula f = Call(F.Id("purityPlusOverlap"), a, psi);
        Formula m = Call(F.Id("conjecturedMin"), n, Card(a));
        Formula lower = AllIn(psi, States(),
            Implies(unit, Rel(m, FormulaRelationOperator.LessThanOrEqual, f)));
        Formula attained = SomeIn(psi, States(), And(unit, Equal(f, m)));
        Formula body = AllIn(n, Naturals(),
            Seq(Forall, Sp, a, Sp, Subseteq, Sp, Call(F.Id("Fin"), n), Comma, Sp,
                Implies(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, Card(a)),
                    Implies(Rel(Card(a), FormulaRelationOperator.LessThan, n), And(lower, attained)))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
