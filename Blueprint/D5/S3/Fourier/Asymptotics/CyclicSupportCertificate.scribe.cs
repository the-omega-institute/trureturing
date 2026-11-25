using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicSupportCertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicSupportCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A boundary variation and a finite dual certificate control which cyclic weights are strictly positive.",
        H("Sign certificates for cyclic support"),
        Blocks(
            Describe.Lean(DescribeId.Create("outer-activation-variation"),
                DeclarationHandle.Create(Owner + ".boundary_variation_pos"),
                H("Strict positivity at the outer level"),
                StatementSource.FromAuthor(Boundary()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let T be the largest of the sampled levels xᵢ, with at least one smaller level. " +
                    "For a quadratic variation with zero total mass and positive first moment, " +
                    "eliminate the constant and linear coefficients using those two moment equations. " +
                    "The remaining quadratic term at T is proportional to the sum over ordered pairs " +
                    "of (xᵢ−xⱼ)²(T−xᵢ)(T−xⱼ). This is the numerator of the monic orthogonal quadratic " +
                    "in the pair-average formula. Each summand is nonnegative, while the first moment " +
                    "term is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-cosine-support-certificate"),
                DeclarationHandle.Create(Owner + ".exact_support_of_dual"),
                H("Exact finite support from two excluded levels"),
                StatementSource.FromAuthor(Dual()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quadratic has nonpositive coefficients of the two cosine deficits. " +
                    "Its values are positive on the candidate set and negative at both endpoints bounding " +
                    "the excluded cosines. Convexity implies strict negativity at every excluded sample. " +
                    "The candidate equals the positive part of the polynomial and has mass one and the " +
                    "two exact moments. The squared distance to this candidate is strictly positive for any " +
                    "distinct competitor, and the clipping and moment slack terms are nonnegative."))),
                DescribeRole.Theorem))));

    private static Formula Boundary()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var levels = F.Id("I");
        var x = Call("x", i);
        var T = Call("x", j);
        var r = Call("r", x);
        var atTop = And(All("i", levels, Le(x, T)), Bind(FormulaQuantifier.Exists, "i", levels, Lt(x, T)));
        var sum = new Formula.Subscript(F.Sum, i);
        return F.Disp(F.Seq(Eq(r, Add(Add(F.Id("a"), Multiply(F.Id("b"), x)),
                Multiply(F.Id("g"), new Formula.Power(x, F.D(2))))), F.Comma, F.Sp,
            Logic(And(atTop, And(Le(F.D(0), F.Id("g")), And(Eq(F.Seq(sum, r), F.D(0)),
                Lt(F.D(0), F.Seq(sum, Multiply(x, r)))))),
                FormulaLogicOperator.Implies, Lt(F.D(0), Call("r", T)))));
    }

    private static Formula Dual()
    {
        var q = F.Id("q");
        var a = F.Id("a");
        var b = F.Id("b");
        var g = F.Id("g");
        var s = F.Id("s");
        var threshold = F.Id("alpha");
        var lo = F.Id("L");
        var hi = F.Id("H");
        var i = F.Id("i");
        var c = F.Id("c");
        var w = F.Id("w");
        var v = F.Id("v");
        var sites = F.Id("S");
        var residues = Call("ZMod", q);
        var sampled = Call("c", i);
        var p = Call("p", c);
        var polynomial = Eq(p, Add(Add(a, Multiply(b, Subtract(F.D(1), c))), Multiply(g,
            new Formula.Fraction(Subtract(F.D(1), new Formula.Power(c, F.D(2))), s))));
        var sign = And(Le(b, F.D(0)), And(Le(g, F.D(0)),
            And(Lt(Call("p", lo), F.D(0)), Lt(Call("p", hi), F.D(0)))));
        var outside = All("i", F.Seq(residues, F.Sp, F.Setminus, F.Sp, sites),
            And(Le(lo, sampled), Le(sampled, hi)));
        var pos = All("i", sites, Lt(F.D(0), Call("p", sampled)));
        var mass = Eq(F.Seq(new Formula.Subscript(F.Sum, i), Call("v", i)), F.D(1));
        var moments = And(Eq(Call("M", F.D(1), v), threshold), Eq(Call("M", F.D(2), v), threshold));
        var feasible = Call("Feasible", q, threshold);
        var different = new Formula.Relation(w, FormulaRelationOperator.NotEqual, v);
        var strict = All("w", feasible, Logic(different, FormulaLogicOperator.Implies,
            Lt(Call("E", v), Call("E", w))));
        var exact = All("w", feasible, Logic(Call("IsMinOn", F.Id("E"), feasible, w),
            FormulaLogicOperator.Implies, All("i", residues,
                Logic(Lt(F.D(0), Call("w", i)), FormulaLogicOperator.Iff, Mem(i, sites)))));
        var hypotheses = And(And(Lt(F.D(0), q), Lt(F.D(0), s)),
            And(sign, And(outside, And(pos, And(mass, moments)))));
        return F.Disp(F.Seq(polynomial, F.Comma, F.Sp, Eq(v, Call("Restrict", F.Id("p"), F.Id("c"), sites)),
            F.Comma, F.Sp, Logic(hypotheses, FormulaLogicOperator.Implies,
                And(Mem(v, feasible), And(strict, exact)))));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, domain, body);
    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.BindMany(kind, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
}
