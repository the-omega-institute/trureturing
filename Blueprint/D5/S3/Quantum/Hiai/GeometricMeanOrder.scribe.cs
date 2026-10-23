using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;

internal sealed class GeometricMeanOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "GeometricMeanOrder", H("GeometricMeanOrder"), Blocks(
            Describe.Lean(DescribeId.Create("mean-eq-operatorpowermean"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_eq_operatorPowerMean"),
                H("Base convention"), StatementSource.FromAuthor(Convention()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every complete nontrivial complex Hilbert space, nonnegative A and strictly positive B, the base-first genuine mean equals operatorPowerMean(theta,1,A,B). No order of multiplication is reversed. The inner congruence is nonnegative and all inverse powers apply to the strictly positive base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-jointlyconcave"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_jointlyConcave"),
                H("Joint mean concavity"), StatementSource.FromAuthor(Concavity()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("For every theta in [0,1] the genuine mean is jointly operator concave on the strictly positive cone. The existing all-Hilbert perspective theorem supplies this inequality with the local base in its second argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono-left"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_left"),
                H("Monotonicity of the base"), StatementSource.FromAuthor(MonoLeft()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("If B <= Bprime are strictly positive and A is nonnegative, increasing B increases its genuine mean with A for every theta in [0,1]. Set C=sqrt(B) sqrt(Bprime inverse); C adjoint C <= I. Contraction Jensen for the negative power function gives the required middle inequality. Congruence by sqrt(Bprime) cancels the invertible factors. No B/A commutation is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono-right"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono_right"),
                H("Monotonicity of the other input"), StatementSource.FromAuthor(MonoRight()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("Increasing A increases the genuine mean with fixed B, for theta in [0,1]. Loewner-Heinz monotonicity is applied between the two square-root congruences. The both-input theorem uses this inequality after increasing the base."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mean-mono"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/GeometricMeanOrder.mean_mono"),
                H("Both-input order"), StatementSource.FromAuthor(Mono()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Divergence/hiai2015meanconcavity")),
                Blocks(Paragraph(Text("Increasing both strictly positive bases and the nonnegative second inputs increases the mean for theta in [0,1]. The comparison composes base monotonicity and Loewner-Heinz monotonicity."))), DescribeRole.Theorem),
            Paragraph(Text("These are classical operator-mean and tracial variational arguments. The source dependencies retain their attribution and licenses. Full Hiai Problem 5.18 additionally requires inverse-geometric identification, its original parameter assembly and the support-preserving positive semidefinite extension.")))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Id(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(Id("C")));
    private static Formula Op => Call("L", Id("H"));
    private static Formula Bind(Formula type, string[] names, Formula body)
    {
        var items = new List<Formula> { Forall, Sp };
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(Id(names[i]));
        }
        items.AddRange([Colon, Sp, type, Comma, Esc, body]);
        return Seq([.. items]);
    }
    private static Formula And(params Formula[] facts)
    {
        var items = new List<Formula>();
        for (var i = 0; i < facts.Length; i++)
        {
            if (i > 0) items.AddRange([Land, Sp]);
            items.Add(facts[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Imp(Formula hypothesis, Formula conclusion) =>
        Seq(hypothesis, Implies, Esc, conclusion);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Leq(Formula x, Formula y) => Seq(x, Le, Sp, y);
    private static Formula UnitInterval(Formula x) => And(Leq(D(0), x), Leq(x, D(1)));
    private static Formula Pd(Formula x) => Call("pdSet", x);
    private static Formula Hilbert(Formula body, bool finite = false)
    {
        var h = Id("H");
        var items = new List<Formula>();
        foreach (var instance in new[] { Call("NormedAddCommGroup", h),
            Call("InnerProductSpace", Complex, h), Call("CompleteSpace", h), Call("Nontrivial", h) })
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        if (finite) items.AddRange([OpenBracket, Call("FiniteDimensional", Complex, h),
            CloseBracket, Comma, Sp]);
        items.Add(body);
        return Bind(Call("Level"), ["u"], Bind(Call("Type", Id("u")), ["H"], Seq([.. items])));
    }

    private static Formula Mean(Formula theta, Formula b, Formula a) => Call("mean", theta, b, a);
    private static Formula Convention()
    {
        var theta=Id("theta"); var a=Id("A"); var b=Id("B");
        return Hilbert(Bind(Real, ["theta"], Bind(Op, ["A", "B"],
            Imp(And(Pd(b), Leq(D(0), a)), Eqn(Mean(theta,b,a),
                Call("operatorPowerMean", theta,D(1),a,b))))));
    }
    private static Formula Concavity()
    {
        var theta=Id("theta"); var a=Id("A"); var b=Id("B");
        return Hilbert(Bind(Real, ["theta"], Imp(UnitInterval(theta),
            Call("JointlyConcaveOn", Call("pdCone",Op), Call("pdCone",Op),
                Seq(LambdaLower, Sp, b, Comma, Sp, a, Mapsto, Sp, Mean(theta,b,a))))));
    }
    private static Formula MonoLeft()
    {
        var theta=Id("theta"); var a=Id("A"); var b=Id("B"); var c=Id("C");
        return Hilbert(Bind(Real,["theta"],Bind(Op,["A","B","C"],
            Imp(And(UnitInterval(theta),Pd(b),Pd(c),Leq(D(0),a),Leq(b,c)),
                Leq(Mean(theta,b,a),Mean(theta,c,a))))));
    }
    private static Formula MonoRight()
    {
        var theta=Id("theta"); var a=Id("A"); var b=Id("B"); var c=Id("C");
        return Hilbert(Bind(Real,["theta"],Bind(Op,["A","B","C"],
            Imp(And(UnitInterval(theta),Leq(a,c)),Leq(Mean(theta,b,a),Mean(theta,b,c))))));
    }
    private static Formula Mono()
    {
        var theta=Id("theta"); var a=Id("A"); var b=Id("B"); var c=Id("C"); var e=Id("E");
        return Hilbert(Bind(Real,["theta"],Bind(Op,["A","B","C","E"],
            Imp(And(UnitInterval(theta),Pd(b),Pd(c),Leq(D(0),a),Leq(b,c),Leq(a,e)),
                Leq(Mean(theta,b,a),Mean(theta,c,e))))));
    }
}
