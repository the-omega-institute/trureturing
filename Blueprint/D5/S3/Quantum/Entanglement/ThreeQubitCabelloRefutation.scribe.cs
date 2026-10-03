using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ThreeQubitCabelloRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/ThreeQubitCabelloRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/cereceda2017cabello");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuinely entangled three-qubit state with rational amplitudes, measured with sigma_z and with an observable whose eigenvectors are (3, 4)/5 and (-4, 3)/5 on every qubit, satisfies the three vanishing conditions of Cabello's argument with Q > 0 and gives C = P - Q = 3209679/22562500, which exceeds 9/64. This refutes the conjecture of J. L. Cereceda (arXiv:1609.04763) that 9/64 is the maximum of C over all three-qubit states and local observables.",
        H("A three-qubit violation of Cabello's argument beyond 9/64"),
        Blocks(
            Node("amp", "The amplitude of a product vector", AmpFormula(),
                "For vectors a, b, c of C^2 and a three-qubit vector psi, given by its coordinates psi_ijk with i, j, k in Fin 2, amp(a, b, c, psi) is the inner product of a tensor b tensor c with psi, where the bar is complex conjugation (star in Lean).",
                "amp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("prob", "The joint probability", ProbFormula(),
                "For a unit vector psi, prob(a, b, c, psi) is the probability of the three outcomes whose eigenvectors are a, b and c, the squared modulus of the amplitude (Complex.normSq in Lean).",
                "prob", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isonb", "Local observables", OnbFormula(),
                "A plus-or-minus-one valued projective qubit observable is given by its eigenvectors e for the outcome +1 and f for the outcome -1, which form an orthonormal basis of C^2.",
                "IsONB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cut1", "Product across the first cut", CutFormula(F.Id("ProductCut1"), F.Id("i"), F.Id("j"), F.Id("k")),
                "psi is a product across the cut separating qubit 1 from qubits 2 and 3 when psi_ijk = a_i b_jk for some a and b.",
                "ProductCut1", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("cut2", "Product across the second cut", CutFormula(F.Id("ProductCut2"), F.Id("j"), F.Id("i"), F.Id("k")),
                "psi is a product across the cut separating qubit 2 from qubits 1 and 3 when psi_ijk = a_j b_ik for some a and b.",
                "ProductCut2", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("cut3", "Product across the third cut", CutFormula(F.Id("ProductCut3"), F.Id("k"), F.Id("i"), F.Id("j")),
                "psi is a product across the cut separating qubit 3 from qubits 1 and 2 when psi_ijk = a_k b_ij for some a and b.",
                "ProductCut3", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("genuine", "Genuine entanglement", GenuineFormula(),
                "psi is genuinely entangled when it is a product across none of the three cuts. The claim below assumes it, which only weakens the claim: the paper states the conjecture over all possible states and, in its conclusions, over all entangled states.",
                "GenuinelyEntangled", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every genuinely entangled unit vector psi and all observables U_k, D_k on the qubits k = 1, 2, 3, with eigenvectors up(k), um(k) and dp(k), dm(k), if P(D_1,U_2,U_3|+++) = P(U_1,D_2,U_3|+++) = P(U_1,U_2,D_3|+++) = 0 and Q = P(D_1,D_2,D_3|---) > 0, then C = P(U_1,U_2,U_3|+++) - Q is at most 9/64. The paper conjectures that 9/64 is the maximum of C under these conditions, which contains this bound. In Lean the qubits are indexed by Fin 3 from 0.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A state beyond 9/64", Disp(new Formula.Not(F.Id("claim"))),
                "Take U_k = sigma_z, with eigenvectors (1, 0) and (0, 1), and D_k with eigenvectors (3, 4)/5 and (-4, 3)/5 on every qubit, and psi = (16|000> - 12(|001> + |010> + |100>) - 15(|011> + |101> + |110>) + 9|111>)/38, a unit vector since 16^2 + 3 * 12^2 + 3 * 15^2 + 9^2 = 38^2. Each constraint amplitude is (3 * 16 - 4 * 12)/(5 * 38) = 0. P = (16/38)^2 = 64/361, the amplitude of D_1 D_2 D_3 with outcomes - is -889/4750, so Q = 790321/22562500 > 0, and C = 3209679/22562500, which exceeds 9/64 by 589239/361000000. psi is genuinely entangled: across each cut a 2 x 2 determinant of its coordinates is (16 * (-15) - (-12) * (-12))/38^2, not 0. The sums are evaluated by norm_num.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cereceda-2017-three-qubit-cabello-maximum"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("cabello3-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Conj(Formula value) => Seq(Overline, Grp(value));
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Psi3(Formula i, Formula j, Formula k) => Sub(Psi, Seq(i, j, k));
    private static Formula Sums(Formula body) =>
        Seq(F.Sum, Underscore, Grp(F.Id("i")), Sp, F.Sum, Underscore, Grp(F.Id("j")), Sp,
            F.Sum, Underscore, Grp(F.Id("k")), Sp, body);
    private static Formula Inner(Formula e, Formula f) =>
        Seq(F.Sum, Underscore, Grp(F.Id("i")), Sp,
            Times(Conj(Sub(e, F.Id("i"))), Sub(f, F.Id("i"))));
    private static Formula Vec(Formula name, byte index) => Call(name, D(index));
    private static Formula Prob(Formula a, Formula b, Formula c) => Call(F.Id("prob"), a, b, c, Psi);

    private static Formula AmpFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula term = Times(Times(Times(Conj(Sub(F.Id("a"), i)), Conj(Sub(F.Id("b"), j))),
            Conj(Sub(F.Id("c"), k))), Psi3(i, j, k));
        return Disp(Equal(Call(F.Id("amp"), F.Id("a"), F.Id("b"), F.Id("c"), Psi), Sums(term)));
    }

    private static Formula ProbFormula() =>
        Disp(Equal(Call(F.Id("prob"), F.Id("a"), F.Id("b"), F.Id("c"), Psi),
            new Formula.Power(new Formula.Absolute(
                Call(F.Id("amp"), F.Id("a"), F.Id("b"), F.Id("c"), Psi)), D(2))));

    private static Formula OnbFormula()
    {
        Formula e = F.Id("e"), f = F.Id("f");
        return Disp(Iff(Call(F.Id("IsONB"), e, f),
            And(Equal(Inner(e, e), D(1)), And(Equal(Inner(f, f), D(1)), Equal(Inner(e, f), D(0))))));
    }

    private static Formula CutFormula(Formula name, Formula outer, Formula first, Formula second)
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula product = Times(Sub(F.Id("a"), outer), Sub(F.Id("b"), Seq(first, second)));
        Formula body = Seq(Exists, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp, Forall, Sp,
            i, Comma, Sp, j, Comma, Sp, k, Comma, Sp, Equal(Psi3(i, j, k), product));
        return Disp(Iff(Call(name, Psi), body));
    }

    private static Formula GenuineFormula()
    {
        Formula cut1 = Seq(Neg, Call(F.Id("ProductCut1"), Psi));
        Formula cut2 = Seq(Neg, Call(F.Id("ProductCut2"), Psi));
        Formula cut3 = Seq(Neg, Call(F.Id("ProductCut3"), Psi));
        return Disp(Iff(Call(F.Id("GenuinelyEntangled"), Psi), And(cut1, And(cut2, cut3))));
    }

    private static Formula ClaimFormula()
    {
        Formula up = F.Id("up"), um = F.Id("um"), dp = F.Id("dp"), dm = F.Id("dm"), k = F.Id("k");
        Formula norm = Equal(Sums(new Formula.Power(
            new Formula.Absolute(Psi3(F.Id("i"), F.Id("j"), F.Id("k"))), D(2))), D(1));
        Formula hypotheses = Seq(
            norm, Comma, Sp, Call(F.Id("GenuinelyEntangled"), Psi), Comma, Sp,
            Forall, Sp, k, Comma, Sp, Call(F.Id("IsONB"), Call(up, k), Call(um, k)), Comma, Sp,
            Forall, Sp, k, Comma, Sp, Call(F.Id("IsONB"), Call(dp, k), Call(dm, k)), Comma, Sp,
            Equal(Prob(Vec(dp, 0), Vec(up, 1), Vec(up, 2)), D(0)), Comma, Sp,
            Equal(Prob(Vec(up, 0), Vec(dp, 1), Vec(up, 2)), D(0)), Comma, Sp,
            Equal(Prob(Vec(up, 0), Vec(up, 1), Vec(dp, 2)), D(0)), Comma, Sp,
            Rel(D(0), FormulaRelationOperator.LessThan, Prob(Vec(dm, 0), Vec(dm, 1), Vec(dm, 2))));
        Formula conclusion = Rel(
            Minus(Prob(Vec(up, 0), Vec(up, 1), Vec(up, 2)), Prob(Vec(dm, 0), Vec(dm, 1), Vec(dm, 2))),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Fraction(D(9), D(6, 4)));
        Formula body = Seq(Forall, Sp, Psi, Comma, Sp, up, Comma, Sp, um, Comma, Sp, dp, Comma, Sp, dm,
            Comma, Sp, Parenthesized(hypotheses), Sp, Rightarrow, Sp, conclusion);
        return Disp(Iff(F.Id("claim"), body));
    }

}
