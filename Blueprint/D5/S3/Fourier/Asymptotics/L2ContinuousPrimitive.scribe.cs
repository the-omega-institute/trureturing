using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class L2ContinuousPrimitiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous L2 derivative yields a measurable primitive with continuous paths on its original finite measure space.",
        H("Continuous Integral Versions of L2 Primitives"),
        Blocks(Describe.Lean(
            DescribeId.Create("continuous-ltwo-primitive-modification"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/L2ContinuousPrimitive.result"),
            H("A common set of continuous paths"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let Omega be any measurable space and P a finite measure. "
                    + "Let f and u map the whole real line to real L2(P), with u continuous. "
                    + "Let g(t,z) be jointly measurable and, for every fixed t, equal P-almost "
                    + "everywhere to the chosen representative u(t)(z). Assume, for every real t, "
                    + "f(t)=f(0)+the Bochner integral of u from 0 to t.")),
                Paragraph(Text("Define X(t,z)=f(0)(z)+the oriented integral of g(s,z) from 0 to t. "
                    + "Then X is jointly measurable, its paths on the whole real line are continuous "
                    + "on one common P-almost-everywhere set, and at every fixed t it equals "
                    + "f(t)(z) P-almost everywhere. Equality to arbitrary chosen representatives "
                    + "is only asserted at each fixed time, not simultaneously at all times.")),
                Paragraph(Text("Continuity of u and finiteness of P imply integrability of g "
                    + "on every compact time interval times Omega. Testing against indicator "
                    + "functions in L2 and using Fubini identifies the representative of each "
                    + "Bochner integral. A countable exhaustion by bounded intervals gives one "
                    + "set of locally integrable sample functions, hence continuous primitives. "
                    + "Neither compact product integrability nor separate Bochner integrability "
                    + "is an additional hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula TypedLambda(string name, Formula type, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, F.Sp, type, F.Sp, F.Mapsto, F.Sp, body, F.Close);
    private static Formula For(string name, Formula type, Formula body) =>
        F.Seq(F.Forall, F.Sp, F.Id(name), F.Colon, F.Sp, type, F.Comma, F.Sp,
            F.Open, body, F.Close);
    private static Formula All((string Name, Formula Type)[] binders, Formula body)
    {
        for (int i = binders.Length - 1; i >= 0; i--)
            body = For(binders[i].Name, binders[i].Type, body);
        return body;
    }
    private static Formula Universe(Formula body) =>
        F.Seq(F.Mathrm, F.Grp(F.Id("universe")), F.Sp, F.Id("ell"), F.Semi, F.Sp, body);
    private static Formula TheoremFormula()
    {
        Formula omega = F.Id("Omega"), p = F.Id("P"), x = F.Id("X");
        Formula t = F.Id("t"), z = F.Id("z"), u = F.Id("u"), g = F.Id("g");
        Formula curveType = Arrow(Reals, Call("Lp", Reals, F.D(2), p));
        Formula representativeType = Arrow(Reals, Arrow(omega, Reals));
        Formula heq = For("t", Reals, Call("AlmostEverywhere", p,
            TypedLambda("z", omega, Equal(Call("g", t, z), Call("eval", Call("u", t), z)))));
        Formula hf = For("t", Reals, Equal(Call("f", t),
            F.Seq(Call("f", F.D(0)), F.Sp, F.Plus, F.Sp,
                Call("intervalIntegral", u, F.D(0), t, F.Id("volume")))));
        Formula common = Call("AlmostEverywhere", p, TypedLambda("z", omega,
            Call("Continuous", TypedLambda("t", Reals, Call("X", t, z)))));
        Formula modification = For("t", Reals, Call("AlmostEverywhere", p,
            TypedLambda("z", omega, Equal(Call("X", t, z), Call("eval", Call("f", t), z)))));
        Formula conclusion = new Formula.Logic(Call("Measurable", Call("uncurry", x)),
            FormulaLogicOperator.And, new Formula.Logic(common, FormulaLogicOperator.And, modification));
        Formula integralRepresentative = TypedLambda("t", Reals, TypedLambda("z", omega,
            F.Seq(Call("eval", Call("f", F.D(0)), z), F.Sp, F.Plus, F.Sp,
                Call("intervalIntegral", TypedLambda("s", Reals, Call("g", F.Id("s"), z)),
                    F.D(0), t, F.Id("volume")))));
        Formula letX = F.Seq(F.Mathrm, F.Grp(F.Id("let")), F.Sp,
            x, F.Colon, F.Sp, representativeType, F.Sp, F.Colon, F.Eq, F.Sp,
            integralRepresentative, F.Semi, F.Sp, F.Open, conclusion, F.Close);
        return F.Disp(Universe(All([
            ("Omega", Call("Type", F.Id("ell"))),
            ("mOmega", Call("MeasurableSpace", omega)),
            ("P", Call("Measure", omega, F.Id("mOmega"))),
            ("finiteP", Call("IsFiniteMeasure", p)),
            ("f", curveType),
            ("u", curveType),
            ("g", representativeType),
            ("hu", Call("Continuous", u)),
            ("hg", Call("Measurable", Call("uncurry", g))),
            ("heq", heq),
            ("hf", hf)
        ], letX)));
    }
}
