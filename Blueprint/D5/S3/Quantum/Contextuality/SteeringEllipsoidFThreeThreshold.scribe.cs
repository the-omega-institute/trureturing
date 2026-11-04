using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class SteeringEllipsoidFThreeThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.";
    private const string Companion = "D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction";
    private const string SpinOwner = "D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/ducuarasusaskrzypczyk2024hidden");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-setting steering value is at most max(sqrt(3(1 - c)), 1), where c is Bob's steering-ellipsoid centre length. Every centre length below two thirds is attained by a state violating the inequality.",
        H("The sharp centre threshold for three-setting steering"),
        Blocks(
            Node("centre-b", "Bob's steering-ellipsoid centre", CentreBFormula(),
                "Equation (QSEcentre), QC_LI.tex lines 245-261, gives Bob's centre as (b - transpose(T)a)/(1 - |a| squared). Here blochA and blochB are the two Bloch vectors, corr is the real correlation matrix and vlen is Euclidean length. When Alice's Bloch vector has length one, the definition assigns Bob's Bloch vector itself, the centre of the single-point ellipsoid. The definition applies to every complex two-qubit matrix.",
                "centreB", AssessedProvenance.FromLiterature(Source)),
            Node("f-three-values", "Three-setting steering values", FThreeValuesFormula(),
                "The steering expression in QC_LI.tex lines 190-203 uses three unit Alice directions. Bob's directions form a real orthonormal frame; spin maps a real direction to its Pauli observable. The value set contains the complex norm of the sum of the three expectations, divided by sqrt(3). Equation (CAC), lines 209-214, gives the optimum in terms of the three singular values. The orthonormal-frame formulation expresses this optimum while allowing Bob's frame to vary.",
                "fThreeValues", AssessedProvenance.FromLiterature(Source)),
            Node("f-three", "The maximal three-setting value", FThreeFormula(),
                "The maximal steering value is the real supremum of fThreeValues. This is the maximal F3 violation of Equation (CAC), QC_LI.tex lines 209-214, with the value set specified above. For a Hermitian matrix the set is nonempty and bounded above; no maximizer is assumed.",
                "fThree", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "A centre bound and its exact violation threshold", ClaimFormula(),
                "The QSE conjecture in QC_LI.tex lines 282-288 asks for a bound depending only on Bob's centre length and reports a numerical impossibility threshold of 0.66. The proposition specifies a centre-only upper bound for every positive semidefinite trace-one two-qubit matrix and requires a violating state at every real centre length t with 0 <= t < 2/3. It gives the exact threshold two thirds; it does not assert that the displayed upper bound is the optimal value at each fixed centre length.",
                "claim", AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("f3-centre-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The bound and the sharp threshold"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Swapping the two tensor factors preserves traces and positivity, interchanges the two Bloch vectors, transposes the correlation matrix and interchanges the two ellipsoid centres. Write T for corr(rho), E for the sum of its squared real entries, and |x| for vlen(x). For an orthonormal frame beta, its row matrix O satisfies O times transpose(O) = I and hence transpose(O) times O = I. Applying this identity to each row of T gives sum_i |T beta_i| squared = E.")),
                    Paragraph(Text(
                        "For a Hermitian rho, bell_trace_real_expansion with the second Alice and Bob directions zero identifies tr(rho (spin(a) tensor spin(b))) with the real number a dot T b embedded in the complex numbers. The triangle inequality and unit_dot_le bound the absolute sum of the three correlations by sum_i |T beta_i|. Cauchy-Schwarz bounds the latter by sqrt(3) sqrt(E). The value set is nonempty, using a constant Alice direction and the coordinate frame, and this estimate bounds it above. Taking its supremum gives F3(rho) <= sqrt(E).")),
                    Paragraph(Text(
                        "For a positive semidefinite trace-one rho, put b = blochB(rho), r = |b| squared, c = |centre(rho)| and Delta = delta(rho). Each flipped state obtained by conjugating the transpose of rho by flipMatrix(n) is positive semidefinite. Consequently Re tr(rho flipped(rho,n)) is nonnegative. Apply flip_purity_identity to each of the three coordinate unit vectors and sum: each squared column length of T occurs once, giving 2E + r <= 3 + 6Delta. The estimate delta_le_centre gives Delta <= (1 - r)(1/2 - c), so E <= 3 - 3c + (3c - 2)r. The estimate bob_radius_le gives 0 <= r <= 1. If 3c - 2 is nonnegative the affine expression is at most 1; otherwise it is at most 3(1 - c). Thus E <= max(3(1 - c), 1). Apply this inequality to the swapped state: its Alice centre is centreB(rho), and transposition preserves E. Monotonicity of the square root and the preceding steering estimate prove the first clause.")),
                    Paragraph(Text(
                        "To obtain a violation for a diagonal correlation matrix diag(p,-p,q) with 2 p² + q² > 1, put c = sqrt(3)/3 and choose the three Bob directions ((1+c)/2,(c-1)/2,c), ((c-1)/2,(1+c)/2,c), and (-c,-c,c). Since c squared = 1/3 these directions are orthonormal, and their images under T all have length L = sqrt((2 p² + q²)/3) > 0. Choose each Alice direction to be T beta_i divided by its length. Each expectation is L, so the value is 3L/sqrt(3) > 1 and is bounded above by F3(rho).")),
                    Paragraph(Text(
                        "For 0 <= t < 2/3 put D = 2 - 2t - t squared and s = t(1-t)/D. These inequalities imply D > 0 and 0 <= s < 1. The state tightState(t,s) is positive semidefinite and has trace one; tight_readouts gives its Bloch vectors (0,0,t+(1-t)s), (0,0,s), and correlation matrix diag(p,-p,q), where p = sqrt(1+s) sqrt((1-t)(1-s)) and q = 1-t+ts. The identity (2 p² + q² - 1)D = (2 - 3t)² shows that its correlation energy exceeds one. Swap its two tensor factors. The matrix remains positive semidefinite with trace one, its Bob centre length is t by tight_centre, and its diagonal correlation matrix is unchanged by transposition. The balanced directions just constructed therefore give F3 > 1, proving the second clause."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ducuara-susa-skrzypczyk-2024-f3-steering-ellipsoid-threshold"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("f3-centre-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => name switch
    {
        "ρ" => Rho,
        "α" => Alpha,
        "β" => Beta,
        _ => F.Id(name),
    };
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Qualified(params string[] parts)
    {
        Formula result = Seq(Operatorname, Grp(X(parts[0])));
        for (var i = 1; i < parts.Length; i++)
            result = Seq(result, Dot, Operatorname, Grp(X(parts[i])));
        return result;
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Local(string name, params Formula[] arguments) => At(Qualified(name), arguments);
    private static Formula External(string owner, string name, params Formula[] arguments) =>
        At(Qualified([.. owner.Split('.'), name]), arguments);
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula Fin(byte n) => At(Qualified("Fin"), D(n));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Direction() => Arrow(Fin(3), Reals());
    private static Formula Settings() => Arrow(Fin(3), Direction());
    private static Formula TwoQubit() => Qualified("D5", "S3", "QuantumBounds", "CHSHWitness", "TwoQubitMatrix");
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), Fin(3))), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(params Formula[] clauses)
    {
        Formula body = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            body = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, Parenthesized(body));
        return body;
    }
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Vlen(Formula value) => External(Companion, "vlen", value);
    private static Formula BlochA(Formula value) => External(Companion, "blochA", value);
    private static Formula BlochB(Formula value) => External(Companion, "blochB", value);
    private static Formula Corr(params Formula[] arguments) => External(Companion, "corr", arguments);
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula Positive(Formula value) => At(Qualified("Matrix", "PosSemidef"), value);
    private static Formula SqrtOf(Formula value) => At(Qualified("Real", "sqrt"), value);

    private static Formula CentreBFormula()
    {
        Formula rho = X("ρ"), i = X("i"), j = X("j");
        Formula numerator = Sub(At(BlochB(rho), j), SumOver("i", Mul(Corr(rho, i, j), At(BlochA(rho), i))));
        Formula body = At(Qualified("ite"), Equal(Vlen(BlochA(rho)), D(1)), BlochB(rho),
            LambdaOf("j", Fin(3), new Formula.Fraction(numerator, Sub(D(1), Square(Vlen(BlochA(rho)))))));
        return All("ρ", TwoQubit(), Equal(Typed(Local("centreB", rho), Direction()), body));
    }

    private static Formula FThreeValuesFormula()
    {
        Formula rho = X("ρ"), r = X("r"), alpha = X("α"), beta = X("β"), i = X("i"), j = X("j");
        Formula unit = All("i", Fin(3), Equal(Vlen(At(alpha, i)), D(1)));
        Formula orthogonal = All("i", Fin(3), All("j", Fin(3), Equal(
            At(Qualified("dotProduct"), At(beta, i), At(beta, j)),
            At(Qualified("ite"), Equal(i, j), Typed(D(1), Reals()), Typed(D(0), Reals())))));
        Formula observable = At(Qualified("Matrix", "kronecker"),
            External(SpinOwner, "spin", At(alpha, i)), External(SpinOwner, "spin", At(beta, i)));
        Formula value = new Formula.Fraction(new Formula.Norm(SumOver("i", Trace(Mul(rho, observable)))), SqrtOf(D(3)));
        Formula predicate = Some("α", Settings(), Some("β", Settings(), And(unit, orthogonal, Equal(r, value))));
        Formula set = Seq(OpenBrace, Typed(r, Reals()), Sp, Mid, Sp, Parenthesized(predicate), CloseBrace);
        return All("ρ", TwoQubit(), Equal(Typed(Local("fThreeValues", rho), At(Qualified("Set"), Reals())), set));
    }

    private static Formula FThreeFormula() => All("ρ", TwoQubit(),
        Equal(Typed(Local("fThree", X("ρ")), Reals()), At(Qualified("sSup"), Local("fThreeValues", X("ρ")))));

    private static Formula ClaimFormula() => Equal(Typed(Qualified("claim"), Qualified("Prop")), Parenthesized(ClaimBody()));

    private static Formula ClaimBody()
    {
        Formula rho = X("ρ"), t = X("t");
        Formula bound = At(Qualified("max"), SqrtOf(Mul(D(3), Sub(D(1), Vlen(Local("centreB", rho))))), D(1));
        Formula universal = All("ρ", TwoQubit(), Implies(Positive(rho), Implies(Equal(Trace(rho), Typed(D(1), Complexes())),
            LE(Local("fThree", rho), bound))));
        Formula state = Some("ρ", TwoQubit(), And(Positive(rho), Equal(Trace(rho), Typed(D(1), Complexes())),
            Equal(Vlen(Local("centreB", rho)), t), LT(D(1), Local("fThree", rho))));
        Formula threshold = All("t", Reals(), Implies(LE(D(0), t), Implies(LT(t, new Formula.Fraction(D(2), D(3))), state)));
        return And(universal, threshold);
    }
}
