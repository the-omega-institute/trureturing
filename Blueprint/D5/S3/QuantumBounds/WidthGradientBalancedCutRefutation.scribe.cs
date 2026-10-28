using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class WidthGradientBalancedCutRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/WidthGradientBalancedCutRefutation.";
    private const string Module = "D5.S3.QuantumBounds.WidthGradientBalancedCutRefutation";
    private const string LocalOperators = "D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence";
    private const string Paulis = "D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction";
    private const string Separability = "D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/wolk2016entanglementwidth");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four singlets within the two halves of an eight-qubit chain have zero squared total spin and gradient second moment 240, exceeding the proposed balanced-cut bound 48.",
        H("The balanced-cut gradient bound fails for eight qubits"),
        Blocks(
            Paragraph(Text(
                "The chain has N = 2m qubits. Fin m labels the half-sites by 0 through m − 1; "
                    + "the corresponding physical site labels start at one. Matrices act on complex "
                    + "amplitudes over the displayed computational bases. Matrix multiplication "
                    + "and matrix squares are operator multiplication, and a matrix numeral one "
                    + "is the identity. The Kronecker product orders the first half before the second.")),
            Node("sys", "Sys", "The half and system spaces", SysFormula(),
                "Each half has computational basis Fin m → Fin 2 and Hilbert space "
                    + "ℂ^{Fin m → Fin 2}. The system basis is the ordered product of the two "
                    + "half bases, so its Hilbert space is the tensor product of the half spaces. "
                    + "The first factor contains physical sites 1 through m, and the second "
                    + "contains sites m + 1 through 2m.",
                AssessedProvenance.FromRepo(Source)),
            Node("site-op", "siteOp", "An operator at one site", SiteOpFormula(),
                "The operator localOp(j,A) applies A at half-site j and the identity at every "
                    + "other half-site. In the first branch the natural value k.val is read as "
                    + "an element of Fin m; in the second branch k.val − m is read that way. "
                    + "The branch inequalities ensure that these indices lie in Fin m. Thus the "
                    + "first m chain sites act on the first factor. The three Pauli matrices used "
                    + "in Appendix D are displayed below, in the order x, y, z; Complex.I is the "
                    + "imaginary unit and the nested brackets list matrix rows.",
                AssessedProvenance.FromLiterature(Source), PauliFormula()),
            Node("total-spin-sq", "totalSpinSq", "Squared total spin", TotalSpinSqFormula(),
                "For each component ℓ, J_ℓ is the sum of its single-site Pauli operators. "
                    + "The operator J² is the sum of J_ℓ² over x, y, z. This is Pauli "
                    + "normalization, with no factor of one half in J_ℓ, as in the source.",
                AssessedProvenance.FromLiterature(Source)),
            Node("gradient-weight", "gradientWeight", "The linear gradient weights", GradientWeightFormula(),
                "For the one-based physical site q = k.val + 1, the weight is "
                    + "2q − 2m − 1 = 2q − N − 1, as in Appendix D. "
                    + "The arithmetic inside Complex.ofReal is real, and its value is then "
                    + "embedded in ℂ. For m = 4 the weights are −7, −5, −3, −1, 1, 3, 5, 7.",
                AssessedProvenance.FromLiterature(Source)),
            Node("gradient-sq", "gradientSq", "Squared gradient spin", GradientSqFormula(),
                "The gradient component B_ℓ weights each site Pauli by 2q − N − 1. "
                    + "The scalar action SMul.smul multiplies every entry of the site operator. "
                    + "The sum of the three component squares is B².",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The proposed balanced-cut inequality", ClaimFormula(),
                "Appendix D proposes this bound for all density matrices with entanglement "
                    + "only inside the two halves. Here N = 2m, m is any natural number at least "
                    + "two, and a density matrix is positive semidefinite with trace one. "
                    + "The predicate IsSeparable is the finite convex mixture of product density "
                    + "matrices across exactly this factorization, expanded below. The reference "
                    + "values are ⟨B²⟩₋ = 6N, ⟨J²⟩cl = 2N and "
                    + "⟨B²⟩cl = N⁴/4 + 2(N − 1)N(N + 1)/3. The numerator uses this last "
                    + "second moment: the printed ⟨B⟩cl is read as ⟨B²⟩cl, consistently with "
                    + "the stated endpoints. At zero squared total spin this coefficient "
                    + "does not affect the bound. All arithmetic in the inequality is real.",
                AssessedProvenance.FromLiterature(Source), SeparableFormula()),
            Describe.Lean(
                DescribeId.Create("wg-balanced-cut-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A product of singlets violates the bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Local("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take m = 4 and N = 8. In each half let χ be the product of the normalized "
                        + "singlets (|01⟩ − |10⟩)/√2 on half-sites (1,4) and (2,3), using "
                        + "one-based labels. The normalized vector Φ = χ ⊗ χ defines the positive "
                        + "semidefinite density matrix ρ = |Φ⟩⟨Φ| of trace one. It is a product "
                        + "across the balanced cut, hence IsSeparable holds with one term of weight "
                        + "one. Each half is annihilated by every total-spin component, giving "
                        + "⟨J²⟩ = 0. For each ℓ = x, y, z, the gradient component restricted to "
                        + "either half has mean zero and second moment ⟨B_ℓ²⟩ = 40: the paired "
                        + "weight differences have squares 6² and 2². The two half gradients "
                        + "have zero cross term in the product state, so the full component "
                        + "second moment is 80 and ⟨B²⟩ = 3 · (40 + 40) = 240. "
                        + "The proposed inequality of Wölk and Gühne instead gives "
                        + "⟨B²⟩ ≤ 6N = 48 at ⟨J²⟩ = 0. Since 240 > 48, the universal "
                        + "claim is false. The singlets join sites inside each half; separability "
                        + "across the cut permits these nonadjacent pairs."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wolk-guhne-2016-balanced-cut-gradient-bound-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance, Formula? explanation = null) => Describe.Lean(
            DescribeId.Create("wg-balanced-cut-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            explanation is null ? Blocks(Paragraph(Text(prose)))
                : Blocks(Paragraph(Text(prose)), new DocumentBlock.DisplayFormula(explanation)),
            DescribeRole.Definition);

    private static Formula SysFormula()
    {
        Formula m = F.Id("m");
        return All(m, Natural(), Equal(LocalCall("Sys", m),
            Parenthesized(Seq(HalfBasis(m), Sp, Times, Sp, HalfBasis(m)))));
    }

    private static Formula SiteOpFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k"), a = F.Id("A");
        Formula value = Call("Fin.val", k);
        Formula site = LocalCall("siteOp", m, k, a);
        return All(m, Natural(), All(k, Fin(Twice(m)), All(a, QubitMatrix(), And(
            Imp(Less(value, m), Equal(site,
                Kron(Call(LocalOperators + ".localOp", value, a), D(1)))),
            Imp(AtMost(m, value), Equal(site,
                Kron(D(1), Call(LocalOperators + ".localOp", Subtract(value, m), a))))))));
    }

    private static Formula PauliFormula() => And(
        Equal(Pauli(D(0)), Rows(D(0), D(1), D(1), D(0))),
        Equal(Pauli(D(1)), Rows(D(0), new Formula.Negate(Qualified("Complex.I")),
            Qualified("Complex.I"), D(0))),
        Equal(Pauli(D(2)), Rows(D(1), D(0), D(0), new Formula.Negate(D(1)))));

    private static Formula TotalSpinSqFormula()
    {
        Formula m = F.Id("m"), l = F.Id("l"), k = F.Id("k");
        return All(m, Natural(), Equal(LocalCall("totalSpinSq", m),
            SumOver(l, Fin(D(3)), Square(SumOver(k, Fin(Twice(m)),
                LocalCall("siteOp", m, k, Pauli(l)))))));
    }

    private static Formula GradientWeightFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k");
        Formula index = Typed(Add(Call("Fin.val", k), D(1)), Real());
        Formula weight = Subtract(Subtract(Twice(index), Twice(Typed(m, Real()))), D(1));
        return All(m, Natural(), All(k, Fin(Twice(m)),
            Equal(LocalCall("gradientWeight", m, k), Call("Complex.ofReal", weight))));
    }

    private static Formula GradientSqFormula()
    {
        Formula m = F.Id("m"), l = F.Id("l"), k = F.Id("k");
        return All(m, Natural(), Equal(LocalCall("gradientSq", m),
            SumOver(l, Fin(D(3)), Square(SumOver(k, Fin(Twice(m)),
                Call("SMul.smul", LocalCall("gradientWeight", m, k),
                    LocalCall("siteOp", m, k, Pauli(l))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m");
        Formula n = Twice(Typed(m, Real()));
        Formula classical = Add(new Formula.Fraction(new Formula.Power(n, D(4)), D(4)),
            new Formula.Fraction(Multiply(Multiply(Multiply(D(2), Subtract(n, D(1))), n),
                Add(n, D(1))), D(3)));
        Formula slope = new Formula.Fraction(Subtract(classical, Multiply(D(6), n)), Twice(n));
        Formula bound = Add(Multiply(D(6), n),
            Multiply(slope, Expectation(Rho, LocalCall("totalSpinSq", m))));
        return Iff(Local("claim"), All(m, Natural(), Imp(AtMost(D(2), m),
            All(Rho, SystemMatrix(m), Imp(Positive(Rho), Imp(Equal(Trace(Rho), D(1)),
                Imp(Separable(Rho), AtMost(Expectation(Rho, LocalCall("gradientSq", m)), bound))))))));
    }

    private static Formula SeparableFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), p = F.Id("p");
        Formula u = F.Id("U"), v = F.Id("V"), t = F.Id("t");
        Formula weight = Apply(p, t), left = Apply(u, t), right = Apply(v, t);
        Formula terms = And(All(t, Fin(n), AtMost(D(0), weight)),
            Equal(SumOver(t, Fin(n), weight), D(1)),
            All(t, Fin(n), And(Positive(left), Equal(Trace(left), D(1)),
                Positive(right), Equal(Trace(right), D(1)))),
            Equal(Rho, SumOver(t, Fin(n),
                Call("SMul.smul", Call("Complex.ofReal", weight), Kron(left, right)))));
        return All(m, Natural(), All(Rho, SystemMatrix(m), Iff(Separable(Rho),
            Some(n, Natural(), Some(p, Arrow(Fin(n), Real()),
                Some(u, Arrow(Fin(n), HalfMatrix(m)),
                    Some(v, Arrow(Fin(n), HalfMatrix(m)), terms)))))));
    }

    private static Formula Qualified(string name)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }

    private static Formula Local(string name) => Qualified(Module + "." + name);
    private static Formula LocalCall(string name, params Formula[] args) => Apply(Local(name), args);
    private static Formula Call(string name, params Formula[] args) => Apply(Qualified(name), args);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula range) => Parenthesized(new Formula.TypeArrow(domain, range));
    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula HalfBasis(Formula m) => Arrow(Fin(m), Fin(D(2)));
    private static Formula HalfMatrix(Formula m) => Call("Matrix", HalfBasis(m), HalfBasis(m), Complex());
    private static Formula SystemMatrix(Formula m) => Call("Matrix", LocalCall("Sys", m), LocalCall("Sys", m), Complex());
    private static Formula QubitMatrix() => Call("Matrix", Fin(D(2)), Fin(D(2)), Complex());
    private static Formula Pauli(Formula l) => Call(Paulis + ".pauli", l);
    private static Formula Kron(Formula left, Formula right) => Call("Matrix.kronecker", left, right);
    private static Formula Trace(Formula value) => Call("Matrix.trace", value);
    private static Formula Positive(Formula value) => Call("Matrix.PosSemidef", value);
    private static Formula Separable(Formula value) => Call(Separability + ".IsSeparable", value);
    private static Formula Expectation(Formula state, Formula op) => Call("Complex.re", Trace(Multiply(state, op)));
    private static Formula Twice(Formula value) => Multiply(D(2), value);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula SumOver(Formula name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(name, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Rows(Formula a, Formula b, Formula c, Formula d) =>
        Seq(OpenBracket, OpenBracket, a, Comma, Sp, b, CloseBracket, Comma, Sp,
            OpenBracket, c, Comma, Sp, d, CloseBracket, CloseBracket);
    private static Formula Add(Formula left, Formula right) => Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Binary(Formula left, FormulaBinaryOperator op, Formula right) =>
        new Formula.Binary(Parenthesized(left), op, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            body = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, Parenthesized(body));
        return body;
    }
}
