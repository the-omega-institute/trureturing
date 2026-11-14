using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectDensityRepairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace and all-effect lower bounds repair any Hermitian candidate uniformly.",
        H("Uniform density repair"),
        Blocks(
            Paragraph(Text("In the formulas, Mat(d) is Matrix(Fin(d), Fin(d), C), Id(d) is its identity, Tr is the complex matrix trace, and complex is the real-to-complex embedding. The expression ite(Q,u,v) means u if Q holds and v otherwise. For a Hermiticity proof h, specMap(h,f) applies the real function f to the real eigenvalues in its orthonormal spectral decomposition; hermNegPart(h) uses f(x)=max(-x,0). The proof h retains the matrix A as its dependent parameter. Dots denote matrix multiplication.")),
            Paragraph(Text("All matrices are actual complex square matrices indexed by Fin d. IsEffect E means positive semidefiniteness of E and of identity minus E. The error parameter eta is nonnegative and d is at least one in the repair theorem.")),
            Paragraph(Text("The negative spectral projector bounds the trace of the negative part by eta. If the positive part has positive trace, division by that trace produces a positive matrix with complex trace one. If that trace is zero, a coordinate density supplies the required matrix. The same single matrix works for every effect, with correction at most 3*eta.")),
            Describe.Lean(
                DescribeId.Create("negative-projector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector"),
                H("negativeProjector"),
                StatementSource.FromAuthor(Statement("negativeProjector")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Spectral functional calculus of a Hermitian matrix at the indicator of the negative reals defines its negative spectral projector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-projector-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.negativeProjector_effect"),
                H("negativeProjector effect"),
                StatementSource.FromAuthor(Statement("negativeProjector_effect")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every Hermitian matrix in every natural dimension, its negative spectral projector and the complement of that projector are positive semidefinite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-negative-projector"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.mul_negativeProjector"),
                H("mul negativeProjector"),
                StatementSource.FromAuthor(Statement("mul_negativeProjector")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Multiplying a Hermitian matrix by its negative spectral projector gives the negative of its spectral negative part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psd-effect-pairing-bounds"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.psd_effect_pairing_bounds"),
                H("psd effect pairing bounds"),
                StatementSource.FromAuthor(Statement("psd_effect_pairing_bounds")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an arbitrary positive semidefinite matrix B and every actual effect E, the real part of the complex trace of B*E lies between zero and the real part of the complex trace of B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("psd-trace-real"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.psd_trace_real"),
                H("psd trace real"),
                StatementSource.FromAuthor(Statement("psd_trace_real")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complex trace of every positive semidefinite matrix equals the complex embedding of its real part."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-density-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectDensityRepair.uniform_density_repair"),
                H("uniform density repair"),
                StatementSource.FromAuthor(Statement("uniform_density_repair")),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=1, eta>=0 and actual Hermitian A, an error at most eta in its real trace from one and a lower bound -eta for its real trace pairing with every actual effect imply the existence of one actual positive semidefinite rho with complex trace exactly one, uniformly within 3*eta of A on every actual effect. Both positive-trace and zero-positive-trace branches are included."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, P(Seq(variable, Colon, Sp, type)), Comma, Sp, P(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[index]));
        }
        return Seq([.. items]);
    }
    private static Formula Imp(Formula premise, Formula result) => Seq(P(premise), Sp, Implies, Sp, P(result));
    private static Formula EqTo(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula LtTo(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula Ne(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Add(Formula left, Formula right) => P(Seq(left, Plus, right));
    private static Formula Sub(Formula left, Formula right) => P(Seq(left, Minus, right));
    private static Formula Mul(Formula left, Formula right) => P(Seq(left, Sp, Cdot, Sp, right));
    private static Formula Scale(Formula scalar, Formula value) => P(Seq(scalar, Sp, Cdot, Sp, value));
    private static Formula Pow(Formula value, Formula exponent) => Seq(P(value), Caret, Grp(exponent));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert, Sp);
    private static Formula At(Formula function, params Formula[] arguments) =>
        Seq(function, P(Seq(JoinArguments(arguments))));
    private static Formula[] JoinArguments(Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        return [.. items];
    }
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, Colon, Sp, type)), Sp, P(body));
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Pair(Formula left, Formula right) => P(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
    private static Formula Lambda(Formula variable, Formula type, Formula body) =>
        P(Seq(P(Seq(variable, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Inst(string name, Formula type, Formula body) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp, P(body));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin(Formula dimension) => Call("Fin", dimension);
    private static Formula Mat(Formula dimension) => Call("Mat", dimension);
    private static Formula Identity(Formula dimension) => Call("Id", dimension);
    private static Formula Psd(Formula value) => Call("PosSemidef", value);
    private static Formula Hermitian(Formula value) => Call("IsHermitian", value);
    private static Formula Effect(Formula value, Formula dimension) => And(Psd(value), Psd(Sub(Identity(dimension), value)));
    private static Formula Trace(Formula value) => Call("Tr", value);
    private static Formula RealPart(Formula value) => Seq(Re, Sp, P(value));
    private static Formula Born(Formula density, Formula value) => RealPart(Trace(Mul(density, value)));
    private static Formula Density(Formula value) => And(Psd(value), EqTo(Trace(value), D(1)));

    private static Formula Statement(string name)
    {
        Formula d = V("d"), a = V("A"), b = V("B"), e = V("E"), h = V("h"), x = V("x"), eta = V("eta"), rho = Rho;
        Formula matrix = Mat(d), negative = Call("negativeProjector", h);
        Formula Dimensions(Formula body) => All(d, Nat, body);
        Formula HermitianInput(Formula body) => Dimensions(All(a, matrix, All(h, Hermitian(a), body)));
        Formula body = name switch
        {
            "negativeProjector" => HermitianInput(EqTo(negative, Call("specMap", h,
                Lambda(x, Real, Call("ite", LtTo(x, D(0)), D(1), D(0)))))),
            "negativeProjector_effect" => HermitianInput(Effect(negative, d)),
            "mul_negativeProjector" => HermitianInput(EqTo(Mul(a, negative), Seq(Minus, Call("hermNegPart", h)))),
            "psd_effect_pairing_bounds" => Dimensions(All(b, matrix, All(e, matrix,
                Imp(And(Psd(b), Effect(e, d)), And(Le(D(0), Born(b, e)), Le(Born(b, e), RealPart(Trace(b)))))))),
            "psd_trace_real" => Dimensions(All(b, matrix, Imp(Psd(b),
                EqTo(Trace(b), Call("complex", RealPart(Trace(b))))))),
            "uniform_density_repair" => Dimensions(Imp(Le(D(1), d), All(eta, Real, Imp(Le(D(0), eta),
                All(a, matrix, Imp(And(Hermitian(a), Le(Abs(Sub(RealPart(Trace(a)), D(1))), eta),
                    All(e, matrix, Imp(Effect(e, d), Le(Seq(Minus, eta), Born(a, e))))),
                    Some(rho, matrix, And(Density(rho), All(e, matrix, Imp(Effect(e, d),
                        Le(Abs(Sub(Born(rho, e), Born(a, e))), Mul(D(3), eta))))))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        return Disp(body);
    }
}
