using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class L2MeasurableVersionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lipschitz curve in real L2 has a jointly measurable version on its original measure space.",
        H("Jointly Measurable L2 Versions"),
        Blocks(Describe.Lean(
            DescribeId.Create("lipschitz-ltwo-jointly-measurable-version"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/L2MeasurableVersion.result"),
            H("Dyadic representative construction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let Omega be any measurable space, P any measure on Omega, "
                    + "K a nonnegative real number, and f a K-Lipschitz map from the real line "
                    + "to real L2(P). No finiteness or probability assumption on P is needed. "
                    + "The notation f(t)(z) uses the chosen measurable representative of the L2 class.")),
                Paragraph(Text("There is a function X(t,z) measurable for the product sigma-algebra "
                    + "such that, at each fixed real time t, X(t,z)=f(t)(z) for P-almost every z. "
                    + "The exceptional set may depend on t. The conclusion does not assert sample "
                    + "continuity or equality at every time on one common set.")),
                Paragraph(Text("Approximate time t by floor(2^n t)/2^n. Each approximation uses "
                    + "countably many measurable representatives and is jointly measurable. "
                    + "The L2 errors are bounded by K times 2^(-n), hence summable. "
                    + "At every fixed time their representatives converge almost everywhere to f(t). "
                    + "Taking the totalized pointwise limit gives the required jointly measurable X."))),
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
        Formula omega = F.Id("Omega"), p = F.Id("P"), f = F.Id("f"), k = F.Id("K");
        Formula x = F.Id("X"), t = F.Id("t"), z = F.Id("z");
        Formula modification = For("t", Reals,
            Call("AlmostEverywhere", p, TypedLambda("z", omega,
                Equal(Call("X", t, z), Call("eval", Call("f", t), z)))));
        Formula conclusion = F.Seq(F.Exists, F.Sp, x, F.Colon, F.Sp,
            Arrow(Reals, Arrow(omega, Reals)), F.Comma, F.Sp, F.Open,
            new Formula.Logic(Call("Measurable", Call("uncurry", x)),
                FormulaLogicOperator.And, modification), F.Close);
        return F.Disp(Universe(All([
            ("Omega", Call("Type", F.Id("ell"))),
            ("mOmega", Call("MeasurableSpace", omega)),
            ("P", Call("Measure", omega, F.Id("mOmega"))),
            ("f", Arrow(Reals, Call("Lp", Reals, F.D(2), p))),
            ("K", F.Seq(Reals, F.Underscore, F.Grp(F.Ge, F.D(0)))),
            ("hf", Call("LipschitzWith", k, f))
        ], conclusion)));
    }
}
